use std::{io::Write, sync::mpsc::Receiver};
use soft65c02_lib::{LogLine, AddressingMode};
use crate::{AppResult, OutputToken, SymbolTable};

struct LogLineFormatter<'a> {
    log_line: &'a LogLine,
    symbols: Option<&'a SymbolTable>,
}

impl<'a> LogLineFormatter<'a> {
    fn new(log_line: &'a LogLine, symbols: Option<&'a SymbolTable>) -> Self {
        Self { log_line, symbols }
    }

    fn get_adjacent_symbol(&self, addr: u16) -> Option<String> {
        // Only handle zero page addresses
        if addr > 0xFF {
            return None;
        }

        // Check if the address is one more than a symbol
        if let Some(symbols) = self.symbols {
            if addr > 0 {
                let prev_addr = addr - 1;
                if let Some(base_sym) = symbols.get_symbols_for_address(prev_addr).first() {
                    // Only use the adjacent symbol if the current address doesn't have its own symbol
                    if symbols.get_symbols_for_address(addr).is_empty() {
                        return Some(format!("{}+1", base_sym));
                    }
                }
            }
        }
        None
    }

    fn format_addressing_mode(&self, total_width: usize) -> String {
        const ADDR_WIDTH: usize = 9; // (#0xXXXX) is always 9 chars
        let content_width = total_width.saturating_sub(ADDR_WIDTH + 1); // +1 for space before address
        
        let mode_str = format!("{}", self.log_line.resolution.addressing_mode);
        
        // Get symbol for the final target address
        let target_symbol = self.log_line.resolution.target_address.and_then(|addr| {
            // First try direct symbol lookup
            if let Some(sym) = self.symbols.and_then(|symbols| {
                symbols.get_symbols_for_address(addr as u16).first().map(|s| s.to_string())
            }) {
                Some(sym)
            } else {
                // If no direct symbol, try adjacent symbol for zero page
                self.get_adjacent_symbol(addr as u16)
            }
        });

        // Format the address part
        let addr_str = self.log_line.resolution.target_address
            .map(|addr| format!("(#0x{:04X})", addr));

        // Special handling for indirect addressing modes
        match self.log_line.resolution.addressing_mode {
            AddressingMode::ZeroPageIndirectYIndexed(v) | 
            AddressingMode::ZeroPageXIndexedIndirect(v) |
            AddressingMode::ZeroPageIndirect(v) => {
                // Try to get symbol for the base pointer address
                let base_symbol = self.symbols.and_then(|symbols| {
                    symbols.get_symbols_for_address(v[0] as u16).first().map(|s| s.to_string())
                });

                if let Some(sym) = base_symbol {
                    // Format with the symbol replacing the hex address
                    let mode_str = match self.log_line.resolution.addressing_mode {
                        AddressingMode::ZeroPageIndirectYIndexed(_) => format!("({sym}),Y"),
                        AddressingMode::ZeroPageXIndexedIndirect(_) => format!("({sym},X)"),
                        AddressingMode::ZeroPageIndirect(_) => format!("({sym})"),
                        _ => unreachable!()
                    };
                    format!("{:<width$} {}", 
                        mode_str,
                        addr_str.unwrap_or_default(),
                        width = content_width
                    )
                } else {
                    // No symbol for base pointer, use original format
                    format!("{:<width$} {}", 
                        mode_str,
                        addr_str.unwrap_or_default(),
                        width = content_width
                    )
                }
            },
            _ => {
                match (target_symbol, addr_str) {
                    (Some(sym), Some(addr)) => {
                        // If we have both symbol and address
                        match self.log_line.resolution.addressing_mode {
                            AddressingMode::Immediate(_) => {
                                // For immediate mode, keep the #$ prefix
                                format!("{} {:<width$} {}", 
                                    mode_str, 
                                    "", 
                                    addr,
                                    width = content_width.saturating_sub(mode_str.len() + 1)
                                )
                            },
                            _ => {
                                // For other modes, just show the symbol
                                format!("{:<width$} {}", 
                                    sym, 
                                    addr,
                                    width = content_width
                                )
                            }
                        }
                    },
                    (None, Some(addr)) => {
                        // If we only have an address
                        if mode_str.is_empty() {
                            format!("{:>width$} {}", 
                                "", 
                                addr,
                                width = content_width
                            )
                        } else {
                            format!("{:<width$} {}", 
                                mode_str, 
                                addr,
                                width = content_width
                            )
                        }
                    },
                    (Some(sym), None) => {
                        // If we only have a symbol (unusual case)
                        format!("{:<width$}", 
                            sym,
                            width = total_width
                        )
                    },
                    (None, None) => {
                        // If we have neither (e.g., implied addressing)
                        format!("{:<width$}", 
                            mode_str,
                            width = total_width
                        )
                    }
                }
            }
        }
    }

    fn format(&self) -> String {
        // Format the byte sequence
        let mut bytes = vec![self.log_line.opcode];
        bytes.extend(&self.log_line.resolution.operands);
        let byte_sequence = format!(
            "({})",
            bytes
                .iter()
                .fold(String::new(), |acc, s| format!("{} {:02x}", acc, s))
                .trim()
        );

        // Format the final output with debug markers
        format!(
            "#0x{:04X}: {: <12}{: <4} {: <25} {}[{}]",
            self.log_line.address,
            byte_sequence,
            self.log_line.mnemonic,
            self.format_addressing_mode(25),
            self.log_line.outcome,
            self.log_line.cycles
        )
    }
}

pub trait Displayer {
    fn display(&mut self, receiver: Receiver<OutputToken>) -> AppResult<()>;
}

#[derive(Debug, Default)]
pub struct CliDisplayer<T>
where
    T: Write,
{
    output: T,
    verbose: bool,
}

impl<T> CliDisplayer<T>
where
    T: Write,
{
    pub fn new(output: T, verbose: bool) -> Self {
        Self { output, verbose }
    }
}

impl<T> Displayer for CliDisplayer<T>
where
    T: Write + Sync + Send,
{
    fn display(&mut self, receiver: Receiver<OutputToken>) -> AppResult<()> {
        let mut i: u32 = 0;

        while let Ok(token) = receiver.recv() {
            match token {
                OutputToken::Assertion {
                    failure,
                    description,
                } => {
                    i += 1;
                    self.output.write_all(
                        format!(
                            "⚡ {i:02} → {description} {}\n",
                            match failure {
                                None => "✅".to_string(),
                                Some(msg) => format!("❌ ({msg})"),
                            }
                        )
                        .as_bytes(),
                    )?;
                }
                OutputToken::Marker { description } => {
                    self.output
                        .write_all(format!("📄 {description}\n").as_bytes())?;
                }
                OutputToken::Run { loglines, symbols } if self.verbose => {
                    let mut content = String::new();
                    let show_total = loglines.len() > 1;
                    let total_cycles: u32 = if show_total {
                        loglines.iter().map(|l| l.cycles as u32).sum()
                    } else {
                        0
                    };

                    for line in loglines {
                        let formatted = LogLineFormatter::new(&line, symbols.as_ref()).format();
                        content.push_str(&format!("🚀 {}\n", formatted));
                    }

                    if show_total {
                        content.push_str(&format!("🕒 Total cycles: {}\n", total_cycles));
                    }
                    
                    self.output.write_all(content.as_bytes())?;
                }
                OutputToken::Setup(lines) if self.verbose => {
                    self.output
                        .write_all(format!("🔧 {}\n", lines.join("\n")).as_bytes())?;
                }
                OutputToken::View(lines) if self.verbose => {
                    for line in lines {
                        self.output.write_all(format!("🔍 {}\n", line).as_bytes())?;
                    }
                }
                _ => (),
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use soft65c02_lib::{LogLine, AddressingMode, AddressingModeResolution, RegisterState};
    use std::sync::mpsc::channel;

    #[test]
    fn test_symbol_substitution() {
        let mut symbols = SymbolTable::new();
        symbols.add_symbol(0x02C6, "COLOR2".to_string());
        symbols.add_symbol(0x02C8, "COLOR4".to_string());

        // Create a LogLine that references one of these addresses
        let log_line = LogLine {
            address: 0x2002,
            opcode: 0x8d,
            mnemonic: "STA".to_string(),
            resolution: AddressingModeResolution {
                target_address: Some(0x02C6),
                operands: vec![0xC6, 0x02],
                addressing_mode: AddressingMode::Absolute([0xC6, 0x02]),
            },
            outcome: "(0x42)".to_string(),
            cycles: 4,
            registers: RegisterState {
                accumulator: 0x42,
                register_x: 0,
                register_y: 0,
                status: 0,
                stack_pointer: 0xFF,
                command_pointer: 0x2002,
            },
        };

        let formatted = LogLineFormatter::new(&log_line, Some(&symbols)).format();
        assert!(formatted.contains("COLOR2"), "Symbol substitution failed");
        assert_eq!(formatted, "#0x2002: (8d c6 02)  STA  COLOR2          (#0x02C6) (0x42)[4]");
    }

    #[test]
    fn test_adjacent_symbol_substitution() {
        let mut symbols = SymbolTable::new();
        symbols.add_symbol(0x008A, "ptr1".to_string());
        // Deliberately not adding a symbol for 0x8B

        // Create a LogLine that references the address after ptr1
        let log_line = LogLine {
            address: 0x2027,
            opcode: 0x85,
            mnemonic: "STA".to_string(),
            resolution: AddressingModeResolution {
                target_address: Some(0x008B),
                operands: vec![0x8B],
                addressing_mode: AddressingMode::ZeroPage([0x8B]),
            },
            outcome: "(0x20)".to_string(),
            cycles: 3,
            registers: RegisterState {
                accumulator: 0x20,
                register_x: 0,
                register_y: 0,
                status: 0,
                stack_pointer: 0xFF,
                command_pointer: 0x2027,
            },
        };

        let formatted = LogLineFormatter::new(&log_line, Some(&symbols)).format();
        assert!(formatted.contains("ptr1+1"), "Adjacent symbol substitution failed");
        assert_eq!(formatted, "#0x2027: (85 8b)     STA  ptr1+1          (#0x008B) (0x20)[3]");

        // Test that it doesn't substitute if the address has its own symbol
        symbols.add_symbol(0x008B, "ptr2".to_string());
        let formatted = LogLineFormatter::new(&log_line, Some(&symbols)).format();
        assert!(formatted.contains("ptr2"), "Direct symbol should take precedence");
        assert!(!formatted.contains("ptr1+1"), "Adjacent symbol should not be used when direct symbol exists");
    }

    #[test]
    fn test_displayer() {
        // Create a simple buffer to capture output
        let mut buffer = Vec::new();
        let mut displayer = CliDisplayer::new(&mut buffer, true);

        // Create symbol table
        let mut symbols = SymbolTable::new();
        symbols.add_symbol(0x02C6, "COLOR2".to_string());
        symbols.add_symbol(0x02C8, "COLOR4".to_string());

        // Create a channel just for passing the test token
        let (sender, receiver) = channel();

        // Send a run with a LogLine that should have symbol substitution
        let log_line = LogLine {
            address: 0x2027,
            opcode: 0x8d,
            mnemonic: "STA".to_string(),
            resolution: AddressingModeResolution {
                target_address: Some(0x02C8),
                operands: vec![0xC8, 0x02],
                addressing_mode: AddressingMode::Absolute([0xC8, 0x02]),
            },
            outcome: "(0x42)".to_string(),
            cycles: 4,
            registers: RegisterState {
                accumulator: 0x42,
                register_x: 0,
                register_y: 0,
                status: 0,
                stack_pointer: 0xFF,
                command_pointer: 0x2027,
            },
        };
        sender.send(OutputToken::Run { loglines: vec![log_line], symbols: Some(symbols) }).unwrap();
        
        // Drop the sender so the receiver knows there will be no more messages
        drop(sender);
        
        // Process the tokens
        displayer.display(receiver).unwrap();

        // Check the output
        let output = String::from_utf8(buffer).unwrap();
        assert!(output.contains("COLOR4"), "Symbol substitution not found in output");
        assert_eq!(output, "🚀 #0x2027: (8d c8 02)  STA  COLOR4          (#0x02C8) (0x42)[4]\n");
    }
}
