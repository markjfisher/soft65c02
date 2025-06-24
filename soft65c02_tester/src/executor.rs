use std::{
    io::BufRead,
    sync::mpsc::Sender,
};

use anyhow::anyhow;
use soft65c02_lib::{Memory, Registers};

use crate::{AppResult, CliCommand, CliCommandParser, Command, OutputToken, SymbolTable};

#[derive(Debug)]
struct ExecutionRound {
    registers: Registers,
    memory: Memory,
    symbols: Option<SymbolTable>,
    failed: bool,
}

impl Default for ExecutionRound {
    fn default() -> Self {
        let registers = Registers::new(0x0000);
        let memory = Memory::new_with_ram();
        let failed = false;

        Self {
            registers,
            memory,
            symbols: None,
            failed,
        }
    }
}

impl ExecutionRound {
    fn get_mut(&mut self) -> (&mut Registers, &mut Memory, &mut Option<SymbolTable>) {
        (&mut self.registers, &mut self.memory, &mut self.symbols)
    }

    fn is_ok(&self) -> bool {
        !self.failed
    }

    fn set_failed(&mut self) {
        self.failed = true;
    }
}

#[derive(Debug)]
pub struct CommandIterator {
    lines: std::vec::IntoIter<String>,
    symbols: Option<SymbolTable>,
}

impl CommandIterator {
    pub fn new_from_string(input: &str) -> Self {
        // Split input into logical commands by looking for complete statements
        let lines: Vec<String> = Self::split_into_commands(input);
        
        Self { 
            lines: lines.into_iter(),
            symbols: Some(SymbolTable::new()), // Initialize with empty symbol table
        }
    }
    
    fn split_into_commands(input: &str) -> Vec<String> {
        let mut commands = Vec::new();
        let mut current_command = String::new();
        let mut in_string = false;
        let mut escape_next = false;
        
        for line in input.lines() {
            let trimmed = line.trim();
            
            // Skip empty lines and comments when not in a string
            if !in_string && (trimmed.is_empty() || trimmed.starts_with("//")) {
                continue;
            }
            
            if !current_command.is_empty() {
                current_command.push('\n');
            }
            current_command.push_str(line);
            
            // Check if we're in a string literal
            for ch in line.chars() {
                if escape_next {
                    escape_next = false;
                    continue;
                }
                
                match ch {
                    '"' => in_string = !in_string,
                    '\\' if in_string => escape_next = true,
                    _ => {}
                }
            }
            
            // If we're not in a string, this command is complete
            if !in_string {
                commands.push(current_command.trim().to_string());
                current_command.clear();
            }
        }
        
        // Handle any remaining incomplete command
        if !current_command.trim().is_empty() {
            commands.push(current_command.trim().to_string());
        }
        
        commands
    }
}

impl Iterator for CommandIterator {
    type Item = AppResult<CliCommand>;

    fn next(&mut self) -> Option<Self::Item> {
        let command_text = self.lines.next()?;
        
        match CliCommandParser::from_with_context(&command_text, crate::pest_parser::ParserContext::new(self.symbols.as_ref())) {
            Ok(cmd) => {
                // Successfully parsed a command, update symbols if needed
                match &cmd {
                    CliCommand::Memory(crate::commands::MemoryCommand::LoadSymbols { symbols }) => {
                        self.symbols = Some(symbols.clone());
                    }
                    CliCommand::Memory(crate::commands::MemoryCommand::AddSymbol { name, value }) => {
                        if let Some(symtable) = &mut self.symbols {
                            symtable.add_symbol(*value, name.clone());
                        }
                    }
                    _ => {}
                }
                Some(Ok(cmd))
            }
            Err(e) => Some(Err(anyhow!(e)))
        }
    }
}

/// Configuration of the executor.
#[derive(Debug)]
pub struct ExecutorConfiguration {
    /// If true, the executor stops when a command cannot be parsed.
    pub ignore_parse_error: bool,

    /// If true, the executor stops when an assertion fails.
    pub stop_on_failed_assertion: bool,
}

impl Default for ExecutorConfiguration {
    fn default() -> Self {
        Self {
            ignore_parse_error: false,
            stop_on_failed_assertion: true,
        }
    }
}

/// The executor is responsible of running a test file. It sets up memory and
/// registers and maintain them during the execution of the plan. It ensures
/// that the process stops if the Command Pointer register is unchanged after a
/// command execution (if the configuration allows it) or when an error occures.
/// All outputs are sent to a channel receiver.
#[derive(Debug, Default)]
pub struct Executor {
    configuration: ExecutorConfiguration,
}

impl Executor {
    pub fn new(configuration: ExecutorConfiguration) -> Self {
        Self { configuration }
    }

    /// Execute the commands from the buffer and send the outputs to the sender.
    /// The execution stops if an error occurs if the configuration requires it.
    /// The execution stops if the buffer is exhausted. If an assertion fails
    /// and the configuration allows it, the execution stops until the next
    /// marker.
    pub fn run<T: BufRead>(self, mut buffer: T, sender: Sender<OutputToken>) -> AppResult<()> {
        let mut round = ExecutionRound::default();
        let mut failed: usize = 0;
        let mut had_terminated_run = false;

        // Read entire input at once to properly handle multi-line strings
        let mut input = String::new();
        buffer.read_to_string(&mut input)?;
        
        for result in CommandIterator::new_from_string(&input) {
            let command = match result {
                Err(e) if !self.configuration.ignore_parse_error => return Err(anyhow!(e)),
                Err(_) => continue,
                Ok(c) => c,
            };

            if matches!(command, CliCommand::None) {
                continue;
            } else if matches!(command, CliCommand::Marker(_)) {
                round = ExecutionRound::default();
                had_terminated_run = false;
            } else if had_terminated_run || (!round.is_ok() && self.configuration.stop_on_failed_assertion) {
                continue;
            }
            let (registers, memory, symbols) = round.get_mut();
            let token = command.execute(registers, memory, symbols)?;

            // Count both assertion failures and terminated runs as failures
            if matches!(token, OutputToken::Assertion { ref failure, description: _ } if failure.is_some())
                || matches!(token, OutputToken::TerminatedRun { .. })
            {
                failed += 1;
                round.set_failed();
            }

            // Track TerminatedRun separately from other failures
            if matches!(token, OutputToken::TerminatedRun { .. }) {
                had_terminated_run = true;
            }

            sender.send(token)?;
        }

        // buffer is exhausted
        if failed > 0 {
            Err(anyhow!("{failed} assertions failed!"))
        } else {
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::mpsc::channel;

    use super::*;

    #[test]
    fn test_halt_on_error() {
        let configuration = ExecutorConfiguration::default();
        let executor = Executor::new(configuration);
        let buffer = "marker $$first thing$$\nazerty\nassert true $$not executed$$".as_bytes();
        let (sender, receiver) = channel::<OutputToken>();

        let error = executor.run(buffer, sender).unwrap_err();

        assert!(error.to_string().contains("azerty"));
        assert_eq!(1, receiver.iter().count());
    }

    #[test]
    fn test_on_error_continue() {
        let configuration = ExecutorConfiguration {
            ignore_parse_error: true,
            ..ExecutorConfiguration::default()
        };
        let executor = Executor::new(configuration);
        let buffer = "marker $$first thing$$\nazerty\nassert true $$shall pass$$".as_bytes();
        let (sender, receiver) = channel::<OutputToken>();

        executor.run(buffer, sender).unwrap();

        assert_eq!(2, receiver.iter().count());
    }

    #[test]
    fn test_halt_on_assertion_failed() {
        let configuration = ExecutorConfiguration::default();
        let executor = Executor::new(configuration);
        let buffer = "assert false $$first test$$\nassert true $$second test$$\n".as_bytes();
        let (sender, receiver) = channel::<OutputToken>();

        executor.run(buffer, sender).unwrap_err();

        let output = receiver.recv().unwrap();
        assert!(
            matches!(output, OutputToken::Assertion { failure, description } if failure.is_some() && description == *"first test")
        );

        // second test is not executed
        receiver.recv().unwrap_err();
    }

    #[test]
    fn test_continue_when_assertion_succeed() {
        let configuration = ExecutorConfiguration::default();
        let executor = Executor::new(configuration);
        let buffer = "assert true $$first test$$\nassert true $$second test$$\n".as_bytes();
        let (sender, receiver) = channel::<OutputToken>();

        executor.run(buffer, sender).unwrap();

        assert_eq!(2, receiver.into_iter().count());
    }

    #[test]
    fn test_continue_when_assertion_failed() {
        let configuration = ExecutorConfiguration {
            stop_on_failed_assertion: false,
            ..Default::default()
        };
        let executor = Executor::new(configuration);
        let buffer = "assert false $$first test$$\nassert true $$second test$$\n".as_bytes();
        let (sender, receiver) = channel::<OutputToken>();

        executor.run(buffer, sender).unwrap_err();

        assert_eq!(2, receiver.into_iter().count());
    }

    #[test]
    fn test_execution_ok_without_initial_marker() {
        let lines = &[
            "memory write #0x0800 0x(a9,c0)", // LDA $c0
            "run #0x0800",
            "assert A=0xc0 $$accumulator is loaded$$",
        ]
        .join("\n");
        let (sender, receiver) = channel::<OutputToken>();
        let executor = Executor::new(ExecutorConfiguration::default());

        executor.run(lines.as_bytes(), sender).unwrap();

        let output = receiver.recv().unwrap();
        assert!(matches!(output, OutputToken::Setup(_)));

        let output = receiver.recv().unwrap();
        assert!(matches!(output, OutputToken::Run { loglines, symbols } if loglines.len() == 1 && symbols.is_none()));

        let output = receiver.recv().unwrap();
        assert!(
            matches!(output, OutputToken::Assertion { failure, description } if failure.is_none() && description == *"accumulator is loaded")
        );

        assert!(receiver.recv().is_err());
    }

    #[test]
    fn test_execution_ok_with_initial_marker() {
        let lines = &[
            "marker $$load accumulator$$",
            "memory write #0x0800 0x(a9,c0)", // LDA $c0
            "run #0x0800",
            "assert A=0xc0 $$accumulator is loaded$$",
        ]
        .join("\n");
        let (sender, receiver) = channel::<OutputToken>();
        let executor = Executor::new(ExecutorConfiguration::default());

        executor.run(lines.as_bytes(), sender).unwrap();

        let output = receiver.recv().unwrap();
        assert!(matches!(output, OutputToken::Marker { description } if description == *"load accumulator"));

        let output = receiver.recv().unwrap();
        assert!(matches!(output, OutputToken::Setup(_)));

        let output = receiver.recv().unwrap();
        assert!(matches!(output, OutputToken::Run { loglines, symbols } if loglines.len() == 1 && symbols.is_none()));

        let output = receiver.recv().unwrap();
        assert!(
            matches!(output, OutputToken::Assertion { failure, description } if failure.is_none() && description == *"accumulator is loaded")
        );

        assert!(receiver.recv().is_err());
    }

    #[test]
    fn test_with_blank_lines() {
        let lines = &[
            "memory write #0x0800 0x(a9,c0)", // LDA $c0
            "",
            "run #0x0800",
            "   ",
            "assert A=0xc0 $$accumulator is loaded$$",
        ]
        .join("\n");
        let (sender, receiver) = channel::<OutputToken>();
        let executor = Executor::new(ExecutorConfiguration::default());

        executor.run(lines.as_bytes(), sender).unwrap();

        assert_eq!(3, receiver.iter().count());
    }

    #[test]
    fn test_several_plans() {
        let lines = &[
            "registers set A=0xc0",
            "assert A=0xc0 $$accumulator is loaded$$",
            "marker $$second test plan$$",
            "assert A!=0xc0 $$accumulator is random$$",
        ]
        .join("\n");
        let (sender, receiver) = channel::<OutputToken>();
        let executor = Executor::new(ExecutorConfiguration::default());

        let _ = executor.run(lines.as_bytes(), sender);

        let _output = receiver
            .iter()
            .nth(3)
            .expect("there shall be a 4th output token");
    }

    #[test]
    fn several_plans_with_one_failing() {
        let lines = &[
            "marker $$first plan$$",
            "assert false $$failing test$$",
            "assert true  $$must not be executed$$",
            "marker $$second plan$$",
            "assert true  $$must be executed$$",
            "assert false $$failing test$$",
            "marker $$third plan$$",
            "assert true $$must be executed$$",
        ]
        .join("\n");
        let (sender, receiver) = channel::<OutputToken>();
        let executor = Executor::new(ExecutorConfiguration::default());

        executor.run(lines.as_bytes(), sender).unwrap_err();
        let output = receiver
            .iter()
            .nth(2)
            .expect("there shall be a 3th output token");

        assert!(
            matches!(output, OutputToken::Marker { description } if description == *"second plan")
        );
        let output = receiver
            .iter()
            .nth(2)
            .expect("there shall be a 3th output token");

        assert!(
            matches!(output, OutputToken::Marker { description } if description == *"third plan")
        );
    }

    #[test]
    fn test_terminated_run_counts_as_failure() {
        let configuration = ExecutorConfiguration::default();
        let executor = Executor::new(configuration);
        let buffer = "memory write #0x1000 0x(ca,d0,fe)\nrun #0x1000 while cycle_count<5\nassert true $$this should be skipped$$\n".as_bytes();
        let (sender, receiver) = channel::<OutputToken>();

        let error = executor.run(buffer, sender).unwrap_err();
        assert!(error.to_string().contains("1 assertions failed"), "TerminatedRun should count as a failure");

        // Should get the memory write setup and then the terminated run
        let output = receiver.recv().unwrap();
        assert!(matches!(output, OutputToken::Setup(_)));
        
        let output = receiver.recv().unwrap();
        assert!(matches!(output, OutputToken::TerminatedRun { .. }), "Expected TerminatedRun token");

        // No more tokens should be received
        assert!(receiver.recv().is_err(), "Should not receive any more tokens");
    }

    #[test]
    fn test_terminated_run_stops_execution() {
        let configuration = ExecutorConfiguration::default();
        let executor = Executor::new(configuration);
        let buffer = "memory write #0x1000 0x(ca,d0,fe)\nrun #0x1000 while cycle_count<5\nassert true $$should not execute$$\nassert true $$also should not execute$$\n".as_bytes();
        let (sender, receiver) = channel::<OutputToken>();

        executor.run(buffer, sender).unwrap_err();

        // Should get the memory write setup and then the terminated run
        let output = receiver.recv().unwrap();
        assert!(matches!(output, OutputToken::Setup(_)));
        
        let output = receiver.recv().unwrap();
        assert!(matches!(output, OutputToken::TerminatedRun { .. }), "Expected TerminatedRun token");
        
        // Second command should not execute
        assert!(receiver.recv().is_err(), "No more commands should execute after TerminatedRun");
    }

    #[test]
    fn test_terminated_run_continues_after_marker() {
        let configuration = ExecutorConfiguration::default();
        let executor = Executor::new(configuration);
        let buffer = "memory write #0x1000 0x(ca,d0,fe)\nrun #0x1000 while cycle_count<5\nassert true $$should not execute$$\nmarker $$new section$$\nassert true $$should execute$$\nassert true $$should also execute$$\n".as_bytes();
        let (sender, receiver) = channel::<OutputToken>();

        executor.run(buffer, sender).unwrap_err();

        // First section: Setup and TerminatedRun
        let output = receiver.recv().unwrap();
        assert!(matches!(output, OutputToken::Setup(_)));
        
        let output = receiver.recv().unwrap();
        assert!(matches!(output, OutputToken::TerminatedRun { .. }), "Expected TerminatedRun token");
        
        // Second section: Marker and assertions
        let output = receiver.recv().unwrap();
        assert!(matches!(output, OutputToken::Marker { description } if description == "new section"));
        
        let output = receiver.recv().unwrap();
        assert!(matches!(output, OutputToken::Assertion { failure: None, .. }), "First assertion after marker should execute");

        let output = receiver.recv().unwrap();
        assert!(matches!(output, OutputToken::Assertion { failure: None, .. }), "Second assertion after marker should execute");
    }

    #[test]
    fn test_terminated_run_stops_execution_even_with_stop_on_failed_assertion_set_to_false() {
        let configuration = ExecutorConfiguration {
            stop_on_failed_assertion: false,  // This should not affect TerminatedRun behavior
            ..Default::default()
        };
        let executor = Executor::new(configuration);
        let buffer = "memory write #0x1000 0x(ca,d0,fe)\nrun #0x1000 while cycle_count<5\nrun #0x1000 while cycle_count<10\nassert true $$should not execute$$\n".as_bytes();
        let (sender, receiver) = channel::<OutputToken>();

        let error = executor.run(buffer, sender).unwrap_err();
        assert!(error.to_string().contains("1 assertions failed"), "Should only count the first TerminatedRun as a failure");

        let outputs: Vec<OutputToken> = receiver.try_iter().collect();
        // Should get:
        // 1. Setup token
        // 2. First TerminatedRun
        // Nothing else should execute after TerminatedRun
        assert_eq!(outputs.len(), 2, "Should receive only setup and one TerminatedRun");
        assert!(matches!(outputs[0], OutputToken::Setup(_)));
        assert!(matches!(outputs[1], OutputToken::TerminatedRun { .. }));
    }
}
