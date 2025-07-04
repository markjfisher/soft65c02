use std::{fs::File, io::Read, path::PathBuf};

use soft65c02_lib::{execute_step, AddressableIO, LogLine, Memory, Registers};

use crate::{
    until_condition::{Assignment, BooleanExpression},
    symbols::SymbolTable,
    AppResult,
};

#[derive(Debug)]
pub enum OutputToken {
    Assertion {
        failure: Option<String>,
        description: String,
    },
    Marker {
        description: String,
    },
    None,
    Run {
        loglines: Vec<LogLine>,
    },
    Setup(Vec<String>),
}

pub trait Command {
    fn execute(&self, registers: &mut Registers, memory: &mut Memory, symbols: &mut Option<SymbolTable>) -> AppResult<OutputToken>;
}

#[derive(Debug)]
pub enum CliCommand {
    Assert(AssertCommand),
    Marker(String),
    Memory(MemoryCommand),
    None,
    Registers(RegisterCommand),
    Run(RunCommand),
}

impl Command for CliCommand {
    fn execute(&self, registers: &mut Registers, memory: &mut Memory, symbols: &mut Option<SymbolTable>) -> AppResult<OutputToken> {
        match self {
            Self::Assert(command) => command.execute(registers, memory, symbols),
            Self::Marker(comment) => Ok(OutputToken::Marker {
                description: comment.to_owned(),
            }),
            Self::Memory(command) => command.execute(registers, memory, symbols),
            Self::None => Ok(OutputToken::None),
            Self::Registers(command) => command.execute(registers, memory, symbols),
            Self::Run(command) => command.execute(registers, memory, symbols),
        }
    }
}

#[derive(Debug)]
pub struct AssertCommand {
    pub condition: BooleanExpression,
    pub comment: String,
}

impl Command for AssertCommand {
    fn execute(&self, registers: &mut Registers, memory: &mut Memory, _symbols: &mut Option<SymbolTable>) -> AppResult<OutputToken> {
        let token = OutputToken::Assertion {
            failure: self.condition.solve(registers, memory),
            description: self.comment.to_owned(),
        };

        Ok(token)
    }
}

#[derive(Debug)]
pub enum RunAddress {
    Memory(usize),
    InitVector,
}

#[derive(Debug)]
pub struct RunCommand {
    pub stop_condition: BooleanExpression,
    pub start_address: Option<RunAddress>,
}

impl Command for RunCommand {
    fn execute(&self, registers: &mut Registers, memory: &mut Memory, _symbols: &mut Option<SymbolTable>) -> AppResult<OutputToken> {
        if let Some(addr) = &self.start_address {
            match addr {
                RunAddress::InitVector => {
                    let lo = memory.read(0xfffc, 1)?[0] as u16;
                    let hi = memory.read(0xfffd, 1)?[0] as u16;
                    registers.command_pointer = ((hi << 8) | lo) as usize;
                }
                RunAddress::Memory(addr) => registers.command_pointer = *addr,
            };
        }

        let mut loglines: Vec<LogLine> = Vec::new();
        let mut cp = registers.command_pointer;

        loop {
            loglines.push(execute_step(registers, memory)?);

            if registers.command_pointer == cp
                || self.stop_condition.solve(registers, memory).is_none()
            {
                break;
            }
            cp = registers.command_pointer;
        }

        let token = OutputToken::Run { loglines };

        Ok(token)
    }
}

#[derive(Debug)]
pub enum RegisterCommand {
    Flush,
    Set { assignment: Assignment },
}

impl Command for RegisterCommand {
    fn execute(&self, registers: &mut Registers, memory: &mut Memory, _symbols: &mut Option<SymbolTable>) -> AppResult<OutputToken> {
        let outputs = match self {
            Self::Flush => {
                registers.initialize(0x0000);

                vec!["registers flushed".to_string()]
            }
            Self::Set { assignment } => assignment.execute(registers, memory)?,
        };

        let token = OutputToken::Setup(outputs);

        Ok(token)
    }
}

#[derive(Debug)]
pub struct MemorySegment {
    pub address: usize,
    pub data: Vec<u8>,
}

#[derive(Debug)]
pub enum MemoryCommand {
    Flush,
    Load { address: usize, filepath: PathBuf },
    Write { address: usize, bytes: Vec<u8> },
    LoadSegments { segments: Vec<MemorySegment> },
    LoadSymbols { symbols: SymbolTable },
    AddSymbol { name: String, value: u16 },
}

impl Command for MemoryCommand {
    fn execute(&self, _registers: &mut Registers, memory: &mut Memory, symbols: &mut Option<SymbolTable>) -> AppResult<OutputToken> {
        let output = match self {
            Self::Flush => {
                *memory = Memory::new_with_ram();
                Vec::new()
            }
            Self::Write { address, bytes } => match bytes.len() {
                0 => vec!["nothing was written".to_string()],
                1 => {
                    memory.write(*address, bytes)?;
                    vec!["1 byte written".to_string()]
                }
                n => {
                    memory.write(*address, bytes)?;
                    vec![format!("{n} bytes written")]
                }
            },
            Self::Load { address, filepath } => {
                let vec = {
                    let mut f = File::open(filepath)?;
                    let mut buffer: Vec<u8> = vec![];
                    f.read_to_end(&mut buffer)?;

                    buffer
                };
                let buffer = vec;
                memory.write(*address, &buffer).unwrap();

                vec![format!(
                    "{} bytes loaded from '{}' at #0x{address:04X}.",
                    buffer.len(),
                    filepath.display()
                )]
            }
            Self::LoadSegments { segments } => {
                for segment in segments {
                    memory.write(segment.address, &segment.data)?;
                }
                vec![format!("{} segments loaded.", segments.len())]
            }
            Self::LoadSymbols { symbols: new_symbols } => {
                let count = new_symbols.len();
                *symbols = Some(new_symbols.clone());
                vec![format!("{} symbols loaded", count)]
            }
            Self::AddSymbol { name, value } => {
                if let Some(symtable) = symbols {
                    symtable.add_symbol(*value, name.clone());
                    vec![format!("Symbol {} added with value 0x{:04X}", name, value)]
                } else {
                    vec!["No symbol table available".to_string()]
                }
            }
        };

        Ok(OutputToken::Setup(output))
    }
}

#[cfg(test)]
mod assert_command_tests {
    use super::*;

    #[test]
    fn test_assert_command_ok() {
        let command = AssertCommand {
            condition: BooleanExpression::Value(true),
            comment: "nice comment".to_string(),
        };
        let mut registers = Registers::new(0x0000);
        let mut memory = Memory::new_with_ram();
        let token = command.execute(&mut registers, &mut memory, &mut None).unwrap();

        assert!(
            matches!(token, OutputToken::Assertion { failure, description } if failure.is_none() && description == *"nice comment")
        );
    }

    #[test]
    fn test_assert_command_fails() {
        let command = AssertCommand {
            condition: BooleanExpression::Value(false),
            comment: "failing assertion".to_string(),
        };
        let mut registers = Registers::new(0x0000);
        let mut memory = Memory::new_with_ram();

        let token = command.execute(&mut registers, &mut memory, &mut None).unwrap();

        assert!(
            matches!(token, OutputToken::Assertion { failure, description } if failure.is_some() && description == *"failing assertion")
        );
    }
}

#[cfg(test)]
mod run_command_tests {
    use soft65c02_lib::AddressableIO;

    use crate::until_condition::{RegisterSource, Source};

    use super::*;

    #[test]
    fn simple_run() {
        let command = RunCommand {
            stop_condition: BooleanExpression::Value(true),
            start_address: None,
        };
        let mut registers = Registers::new_initialized(0x1000);
        let mut memory = Memory::new_with_ram();
        memory.write(0x1000, &[0xa9, 0xc0]).unwrap(); // LDA #0xc0
        let token = command.execute(&mut registers, &mut memory, &mut None).unwrap();

        assert!(matches!(token, OutputToken::Run { loglines } if loglines.len() == 1));
    }

    #[test]
    fn run_from_addr() {
        let command = RunCommand {
            stop_condition: BooleanExpression::Value(true),
            start_address: Some(RunAddress::Memory(0x1234)),
        };
        let mut registers = Registers::new_initialized(0x0000);
        let mut memory = Memory::new_with_ram();
        memory.write(0x1234, &[0xa9, 0xc0]).unwrap(); // LDA #0xc0
        let token = command.execute(&mut registers, &mut memory, &mut None).unwrap();

        assert!(matches!(token, OutputToken::Run { loglines } if loglines.len() == 1));
    }

    #[test]
    fn run_init_vector() {
        let command = RunCommand {
            stop_condition: BooleanExpression::Value(true),
            start_address: Some(RunAddress::InitVector),
        };
        let mut registers = Registers::new_initialized(0x0000);
        let mut memory = Memory::new_with_ram();
        memory.write(0xfffc, &[0x34, 0x12]).unwrap(); // init vector
        memory.write(0x1234, &[0xa9, 0xc0]).unwrap(); // LDA #0xc0
        let token = command.execute(&mut registers, &mut memory, &mut None).unwrap();

        assert!(matches!(token, OutputToken::Run { loglines } if loglines.len() == 1));
        assert_eq!(0x1236, registers.command_pointer);
        assert_eq!(0xc0, registers.accumulator);
    }

    #[test]
    fn run_with_condition() {
        let command = RunCommand {
            stop_condition: BooleanExpression::StrictlyGreater(
                Source::Register(RegisterSource::RegisterX),
                Source::Value(0),
            ),
            start_address: Some(RunAddress::Memory(0x1234)),
        };
        let mut registers = Registers::new_initialized(0x1000);
        let mut memory = Memory::new_with_ram();
        memory.write(0x1234, &[0xa9, 0xc0, 0xaa]).unwrap(); // LDA #0xc0; TXA
        let token = command.execute(&mut registers, &mut memory, &mut None).unwrap();

        assert!(matches!(token, OutputToken::Run { loglines } if loglines.len() == 2));
    }

    #[test]
    fn run_stops_on_loop() {
        let command = RunCommand {
            stop_condition: BooleanExpression::Value(false),
            start_address: None,
        };
        let mut registers = Registers::new_initialized(0x1000);
        let mut memory = Memory::new_with_ram();
        memory.write(0x1000, &[0xd0, 0b11111110]).unwrap(); // BNE -1
        let token = command.execute(&mut registers, &mut memory, &mut None).unwrap();

        assert!(matches!(token, OutputToken::Run { loglines } if loglines.len() == 1))
    }
}

#[cfg(test)]
mod register_command_tests {
    use crate::until_condition::{RegisterSource, Source};

    use super::*;

    #[test]
    fn test_flush() {
        let command = RegisterCommand::Flush;
        let mut registers = Registers::new_initialized(0xffff);
        let mut memory = Memory::new_with_ram();
        let token = command.execute(&mut registers, &mut memory, &mut None).unwrap();

        assert!(matches!(token, OutputToken::Setup(s) if s[0] == *"registers flushed"));
        assert_eq!(0x0000, registers.command_pointer);
    }

    #[test]
    fn test_set() {
        let command = RegisterCommand::Set {
            assignment: Assignment::new(Source::Value(0xff), RegisterSource::RegisterX),
        };
        let mut registers = Registers::new_initialized(0xffff);
        let mut memory = Memory::new_with_ram();
        let token = command.execute(&mut registers, &mut memory, &mut None).unwrap();

        assert!(matches!(token, OutputToken::Setup(s) if s[0] == *"register X set to 0xff"));
        assert_eq!(0xff, registers.register_x);
    }
}

#[cfg(test)]
mod memory_command_tests {
    use soft65c02_lib::AddressableIO;

    use super::*;

    #[test]
    fn test_flush_command() {
        let command = MemoryCommand::Flush;
        let mut registers = Registers::new_initialized(0x0000);
        let mut memory = Memory::new_with_ram();
        memory.write(0x0000, &[0x01, 0x02, 0x03]).unwrap();
        let token = command.execute(&mut registers, &mut memory, &mut None).unwrap();

        assert_eq!(vec![0x00, 0x00, 0x00], memory.read(0x000, 3).unwrap());
        assert!(matches!(token, OutputToken::Setup(s) if s.is_empty()));
    }

    #[test]
    fn test_write_command() {
        let command = MemoryCommand::Write {
            address: 0x1000,
            bytes: vec![0x01, 0x02, 0x03],
        };
        let mut registers = Registers::new_initialized(0x0000);
        let mut memory = Memory::new_with_ram();
        let token = command.execute(&mut registers, &mut memory, &mut None).unwrap();

        assert!(matches!(token, OutputToken::Setup(v) if v[0] == *"3 bytes written"));
        assert_eq!(
            &[0x01, 0x02, 0x03],
            memory.read(0x1000, 3).unwrap().as_slice()
        );
    }

    #[test]
    fn test_write_no_byte() {
        let command = MemoryCommand::Write {
            address: 0x1000,
            bytes: Vec::new(),
        };
        let mut registers = Registers::new_initialized(0x0000);
        let mut memory = Memory::new_with_ram();
        let token = command.execute(&mut registers, &mut memory, &mut None).unwrap();

        assert!(matches!(token, OutputToken::Setup(s) if s[0] == *"nothing was written"));
        assert_eq!(
            &[0x00, 0x00, 0x00],
            memory.read(0x1000, 3).unwrap().as_slice()
        );
    }

    #[test]
    fn test_write_one_byte() {
        let command = MemoryCommand::Write {
            address: 0x1000,
            bytes: vec![0x01],
        };
        let mut registers = Registers::new_initialized(0x0000);
        let mut memory = Memory::new_with_ram();
        let token = command.execute(&mut registers, &mut memory, &mut None).unwrap();

        assert!(matches!(token, OutputToken::Setup(s) if s[0] == *"1 byte written"));
        assert_eq!(
            &[0x01, 0x00, 0x00],
            memory.read(0x1000, 3).unwrap().as_slice()
        );
    }

    #[test]
    fn test_load() {
        let filepath = PathBuf::new().join("../Cargo.toml");
        let command = MemoryCommand::Load {
            address: 0x1000,
            filepath,
        };
        let mut registers = Registers::new_initialized(0x0000);
        let mut memory = Memory::new_with_ram();
        let token = command.execute(&mut registers, &mut memory, &mut None).unwrap();

        let expected = "bytes loaded from '../Cargo.toml' at #0x1000.".to_owned();
        assert!(matches!(token, OutputToken::Setup(s) if s[0].contains(&expected)));
    }

    #[test]
    fn test_load_segments_empty() {
        let command = MemoryCommand::LoadSegments { 
            segments: Vec::new() 
        };
        let mut registers = Registers::new_initialized(0x0000);
        let mut memory = Memory::new_with_ram();
        let token = command.execute(&mut registers, &mut memory, &mut None).unwrap();

        assert!(matches!(token, OutputToken::Setup(s) if s[0] == *"0 segments loaded."));
    }

    #[test]
    fn test_load_segments_single() {
        let command = MemoryCommand::LoadSegments { 
            segments: vec![
                MemorySegment {
                    address: 0x2000,
                    data: vec![0x01, 0x02, 0x03],
                }
            ] 
        };
        let mut registers = Registers::new_initialized(0x0000);
        let mut memory = Memory::new_with_ram();
        let token = command.execute(&mut registers, &mut memory, &mut None).unwrap();

        // Verify the output token
        assert!(matches!(token, OutputToken::Setup(s) if s[0] == *"1 segments loaded."));
        
        // Verify the memory contents
        assert_eq!(
            &[0x01, 0x02, 0x03],
            memory.read(0x2000, 3).unwrap().as_slice()
        );
    }

    #[test]
    fn test_load_segments_multiple() {
        let command = MemoryCommand::LoadSegments { 
            segments: vec![
                MemorySegment {
                    address: 0x2000,
                    data: vec![0x01, 0x02, 0x03],
                },
                MemorySegment {
                    address: 0x3000,
                    data: vec![0xFF, 0xFE],
                },
                MemorySegment {
                    address: 0x02E0,
                    data: vec![0x34, 0x12],
                }
            ] 
        };
        let mut registers = Registers::new_initialized(0x0000);
        let mut memory = Memory::new_with_ram();
        let token = command.execute(&mut registers, &mut memory, &mut None).unwrap();

        // Verify the output token
        assert!(matches!(token, OutputToken::Setup(s) if s[0] == *"3 segments loaded."));
        
        // Verify each segment was written correctly
        assert_eq!(
            &[0x01, 0x02, 0x03],
            memory.read(0x2000, 3).unwrap().as_slice()
        );
        assert_eq!(
            &[0xFF, 0xFE],
            memory.read(0x3000, 2).unwrap().as_slice()
        );
        assert_eq!(
            &[0x34, 0x12],
            memory.read(0x02E0, 2).unwrap().as_slice()
        );
    }
}
