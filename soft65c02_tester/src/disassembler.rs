use std::collections::{HashMap, HashSet};
use soft65c02_lib::{Memory, CPUInstruction};
use crate::{AppResult, symbols::SymbolTable};

pub struct Disassembler<'a> {
    memory: &'a Memory,
    symbols: &'a mut Option<SymbolTable>,
}

impl<'a> Disassembler<'a> {
    pub fn new(memory: &'a Memory, symbols: &'a mut Option<SymbolTable>) -> Self {
        Self { memory, symbols }
    }

    /// Format an instruction with symbol substitution
    fn format_instruction(&self, instr_str: &str, target_hex: &str, symbols: &[String], max_instr_len: usize) -> String {
        // Helper function for simple symbol replacement with optional comment
        fn do_simple_replacement(instr_str: &str, target_hex: &str, symbols: &[String], max_instr_len: usize) -> String {
            let mut result = instr_str.replace(target_hex, &symbols[0]);
            if symbols.len() > 1 {
                while result.len() < max_instr_len {
                    result.push(' ');
                }
                result.push_str("         ; → ");
                result.push_str(&symbols.join(", "));
            }
            result
        }

        // For non-parenthesized instructions (like direct memory access), just do simple replacement
        if !instr_str.contains('(') {
            return do_simple_replacement(instr_str, target_hex, symbols, max_instr_len);
        }

        // Find the opcode and operands by looking for the first double space
        let (prefix, rest) = match instr_str.find("  ") {
            Some(pos) => (&instr_str[..pos], &instr_str[pos + 2..].trim()),
            None => {
                // If we can't find the expected format, fall back to simple replacement
                return do_simple_replacement(instr_str, target_hex, symbols, max_instr_len);
            }
        };

        // Extract the opcode (everything before the first parenthesis)
        let opcode = match rest.find('(') {
            Some(pos) => rest[..pos].trim(),
            None => {
                // If we can't find the parenthesis, fall back to simple replacement
                return do_simple_replacement(instr_str, target_hex, symbols, max_instr_len);
            }
        };

        // Determine the addressing mode and create the base format
        let base_format = if rest.contains("),Y") {
            format!("{}       {}  ({}),Y", prefix, opcode, &symbols[0])
        } else if rest.contains(",X)") {
            format!("{}       {}  ({},X)", prefix, opcode, &symbols[0])
        } else {
            format!("{}       {}  ({})", prefix, opcode, &symbols[0])
        };

        // Add comment for multiple symbols if needed
        if symbols.len() > 1 {
            let mut result = base_format;
            while result.len() < max_instr_len {
                result.push(' ');
            }
            result.push_str("         ; → ");
            result.push_str(&symbols.join(", "));
            result
        } else {
            base_format
        }
    }

    /// Collect branch targets and addresses with symbols from instructions
    fn collect_targets_and_symbols(
        &self,
        instructions: &[CPUInstruction],
    ) -> (HashSet<usize>, HashMap<usize, String>, HashSet<usize>) {
        let mut branch_targets = HashSet::new();
        let mut branch_labels = HashMap::new();
        let mut addresses_with_symbols = HashSet::new();
        let mut next_branch_id = 1;

        // First collect all addresses that have symbols
        if let Some(symbols) = &self.symbols {
            for instr in instructions.iter() {
                if !symbols.get_symbols_for_address(instr.address as u16).is_empty() {
                    addresses_with_symbols.insert(instr.address);
                }
            }
        }

        // Then handle branch targets that don't have symbols
        for instr in instructions.iter() {
            let instr_str = format!("{}", instr);
            if is_branch_instruction(&instr_str) {
                if let Some(target_addr) = extract_branch_target(&instr_str) {
                    branch_targets.insert(target_addr);
                    // Only create a branch label if the target doesn't have a symbol
                    if !addresses_with_symbols.contains(&target_addr) && !branch_labels.contains_key(&target_addr) {
                        branch_labels.insert(target_addr, format!("branch_{}", next_branch_id));
                        next_branch_id += 1;
                    }
                }
            }
        }

        (branch_targets, branch_labels, addresses_with_symbols)
    }

    /// Generate a formatted line for an instruction, including any labels
    fn format_instruction_line(
        &self,
        instr: &CPUInstruction,
        branch_targets: &HashSet<usize>,
        branch_labels: &HashMap<usize, String>,
        addresses_with_symbols: &HashSet<usize>,
        last_labeled_addr: Option<usize>,
        max_instr_len: usize,
    ) -> (String, Option<usize>) {
        let mut line = String::new();
        let addr = instr.address;

        // Check if this instruction's address has a symbol
        if let Some(symbols) = &self.symbols {
            if last_labeled_addr != Some(addr) {  // Avoid duplicate labels
                let addr_symbols = symbols.get_symbols_for_address(addr as u16);
                if !addr_symbols.is_empty() {
                    line.push_str(&format!("{}:\n", addr_symbols.join(", ")));
                }
            }
        }

        // Check if this is a branch target and doesn't have a symbol
        if branch_targets.contains(&addr) && !addresses_with_symbols.contains(&addr) && last_labeled_addr != Some(addr) {
            if let Some(label) = branch_labels.get(&addr) {
                line.push_str(&format!("{}:\n", label));
            }
        }

        // Add the instruction
        let mut instr_str = format!("{}", instr);
        
        // Handle any memory references (branch, jump, or direct memory access)
        if let Some(target_addr) = extract_branch_target(&instr_str).or_else(|| {
            extract_memory_address(&instr_str)
        }) {
            let target_hex = format!("${:04X}", target_addr);
            // Check if target has a symbol
            if let Some(symbols) = &self.symbols {
                let target_symbols = symbols.get_symbols_for_address(target_addr as u16);
                if !target_symbols.is_empty() {
                    instr_str = self.format_instruction(&instr_str, &target_hex, &target_symbols, max_instr_len);
                } else if let Some(label) = branch_labels.get(&target_addr) {
                    // Use branch label if no symbol exists
                    instr_str = instr_str.replace(&target_hex, label);
                }
            } else if let Some(label) = branch_labels.get(&target_addr) {
                // Use branch label if no symbols exist
                instr_str = instr_str.replace(&target_hex, label);
            }
        }
        
        line.push_str(&instr_str);
        (line, Some(addr))
    }

    pub fn disassemble_range(&self, start: usize, end: usize) -> AppResult<Vec<String>> {
        use soft65c02_lib::disassemble;
        let instructions = disassemble(start, end + 1, self.memory)?;
        let mut output = vec!["---- Start of disassembly ----".to_string()];
        
        // Find the longest instruction for alignment
        let max_instr_len = instructions.iter()
            .map(|instr| format!("{}", instr).len())
            .max()
            .unwrap_or(0);

        // First pass: collect branch targets and symbols
        let (branch_targets, branch_labels, addresses_with_symbols) = 
            self.collect_targets_and_symbols(&instructions);

        // Second pass: Generate output with labels
        let mut last_labeled_addr = None;
        for instr in instructions {
            let (line, new_last_addr) = self.format_instruction_line(
                &instr,
                &branch_targets,
                &branch_labels,
                &addresses_with_symbols,
                last_labeled_addr,
                max_instr_len
            );

            // Split the line into parts if it contains a label
            for part in line.split('\n') {
                output.push(part.to_string());
            }
            
            last_labeled_addr = new_last_addr;
        }
        
        output.push("----- End of disassembly -----".to_string());
        Ok(output)
    }
}

/// Check if an instruction string represents a branch instruction
fn is_branch_instruction(instruction: &str) -> bool {
    static BRANCH_OPCODES: [&str; 8] = ["BCC", "BCS", "BEQ", "BMI", "BNE", "BPL", "BVC", "BVS"];
    BRANCH_OPCODES.iter().any(|&opcode| instruction.contains(opcode))
}

/// Extract the target address from a branch instruction
fn extract_branch_target(instruction: &str) -> Option<usize> {
    // Branch instructions will have a target address in the form "$XXXX"
    if is_branch_instruction(instruction) {
        let dollar_pos = instruction.rfind('$')?;
        let addr_str = &instruction[dollar_pos + 1..];
        let addr_end = addr_str.find(|c: char| !c.is_ascii_hexdigit())
            .unwrap_or(addr_str.len());
        let addr_str = &addr_str[..addr_end];
        
        if let Ok(addr) = usize::from_str_radix(addr_str, 16) {
            return Some(addr);
        }
    }
    None
}

/// Extract a memory address from an instruction string if it references memory directly
/// Returns None for immediate values (#$xx) and other non-memory operations
fn extract_memory_address(instruction: &str) -> Option<usize> {
    // Find the position after the opcode
    let operand_start = instruction.find("  ")?.checked_add(2)?;
    let operands = instruction[operand_start..].trim();

    // Skip immediate addressing mode
    if operands.contains("#$") {
        return None;
    }

    // Handle indirect addressing modes: ($xx),Y and ($xx,X)
    if let Some(paren_start) = operands.find('(') {
        let paren_end = operands.find(')')?;
        let inner_operand = &operands[paren_start + 1..paren_end];
        
        // Handle both ($xx),Y and ($xx,X) forms
        let addr_part = if inner_operand.contains(',') {
            // ($xx,X) form
            inner_operand.split(',').next()?
        } else {
            // ($xx),Y form
            inner_operand
        };
        
        if addr_part.starts_with('$') {
            return usize::from_str_radix(&addr_part[1..], 16).ok();
        }
        return None;
    }

    // Handle zero page and absolute addressing
    // Look for a $ that's not preceded by #
    let dollar_pos = operands.char_indices()
        .find(|(i, c)| *c == '$' && (*i == 0 || !operands[..*i].ends_with('#')))
        .map(|(i, _)| i)?;

    // Parse the hex address after $
    let addr_str = &operands[dollar_pos + 1..];
    let addr_end = addr_str.find(|c: char| !c.is_ascii_hexdigit())
        .unwrap_or(addr_str.len());
    
    usize::from_str_radix(&addr_str[..addr_end], 16).ok()
}

#[cfg(test)]
mod tests {
    use super::*;
    use soft65c02_lib::AddressableIO;

    #[test]
    fn test_disassemble_simple_program() {
        let mut memory = Memory::new_with_ram();
        let mut symbols = None;
        
        // Write a simple program to memory
        memory.write(0x1000, &[0xa9, 0x42, 0x8d, 0x34, 0x12, 0x60]).unwrap();

        let disassembler = Disassembler::new(&memory, &mut symbols);
        let output = disassembler.disassemble_range(0x1000, 0x1005).unwrap();

        let expected_output = "\
---- Start of disassembly ----
#0x1000: (a9 42)       LDA  #$42
#0x1002: (8d 34 12)    STA  $1234
#0x1005: (60)          RTS  
----- End of disassembly -----";

        let actual_output = output.join("\n");
        assert_eq!(actual_output, expected_output, "\nExpected:\n{}\n\nActual:\n{}\n", expected_output, actual_output);
    }

    #[test]
    fn test_disassemble_with_symbols() {
        let mut memory = Memory::new_with_ram();
        let mut symbols = Some(SymbolTable::new());
        
        // Write a simple program to memory
        memory.write(0x1000, &[
            0xa9, 0x42,             // LDA #$42
            0x8d, 0x34, 0x12,       // STA $1234
            0xb1, 0x88,             // LDA ($88),Y
            0x20, 0x00, 0x20,       // JSR $2000
            0x60                    // RTS
        ]).unwrap();
        
        // Add some symbols
        if let Some(symbols) = &mut symbols {
            symbols.add_symbol(0x1000, "start".to_string());
            symbols.add_symbol(0x1000, "main".to_string());  // Multiple symbols for same address
            symbols.add_symbol(0x1234, "COUNTER".to_string());
            symbols.add_symbol(0x0088, "TMP1".to_string());
            symbols.add_symbol(0x2000, "other_func".to_string());
            // this should not match the literal value as we explicitly don't want to mix values with symbols
            symbols.add_symbol(0x42, "VAL1".to_string());
        }

        let disassembler = Disassembler::new(&memory, &mut symbols);
        let output = disassembler.disassemble_range(0x1000, 0x100a).unwrap();

        let expected_output = "\
---- Start of disassembly ----
start, main:
#0x1000: (a9 42)       LDA  #$42
#0x1002: (8d 34 12)    STA  COUNTER
#0x1005: (b1 88)       LDA  (TMP1),Y
#0x1007: (20 00 20)    JSR  other_func
#0x100A: (60)          RTS  
----- End of disassembly -----";

        let actual_output = output.join("\n");
        assert_eq!(actual_output, expected_output, "\nExpected:\n{}\n\nActual:\n{}\n", expected_output, actual_output);
    }

    #[test]
    fn test_disassemble_with_branch() {
        let mut memory = Memory::new_with_ram();
        let mut symbols = Some(SymbolTable::new());
        
        // Write a program with multiple branches
        memory.write(0x1000, &[
            0x18,             // CLC
            0xa9, 0x10,       // LDA #$10
            0x6d, 0x00, 0x20, // ADC $2000
            0x8d, 0x00, 0x20, // STA $2000
            0x90, 0x0D,       // BCC +0D (to branch_1)
            0xee, 0x01, 0x20, // INC $2001
            0xd0, 0x05,       // BNE +5 (to branch_2)
            0xf0, 0xee,       // BEQ -18 (back to start/main)
            0x4c, 0x1b, 0x10, // JMP end
            0xa9, 0x00,       // LDA #$00
            0x60,            // RTS
            0xa9, 0xff,       // LDA #$ff
            0x60,            // RTS
            0xa9, 0x42,       // LDA #$42
            0x60             // RTS (end)
        ]).unwrap();
        
        // Add symbols for memory locations, including multiple symbols for same address
        if let Some(symbols) = &mut symbols {
            symbols.add_symbol(0x1000, "start".to_string());
            symbols.add_symbol(0x1000, "main".to_string());
            symbols.add_symbol(0x2000, "mem_lo".to_string());
            symbols.add_symbol(0x2001, "mem_hi".to_string());
            symbols.add_symbol(0x101b, "end".to_string());
        }

        let disassembler = Disassembler::new(&memory, &mut symbols);
        let output = disassembler.disassemble_range(0x1000, 0x101d).unwrap();

        let expected_output = "\
---- Start of disassembly ----
start, main:
#0x1000: (18)          CLC  
#0x1001: (a9 10)       LDA  #$10
#0x1003: (6d 00 20)    ADC  mem_lo
#0x1006: (8d 00 20)    STA  mem_lo
#0x1009: (90 0d)       BCC  branch_1
#0x100B: (ee 01 20)    INC  mem_hi
#0x100E: (d0 05)       BNE  branch_2
#0x1010: (f0 ee)       BEQ  start         ; → start, main
#0x1012: (4c 1b 10)    JMP  end
branch_2:
#0x1015: (a9 00)       LDA  #$00
#0x1017: (60)          RTS  
branch_1:
#0x1018: (a9 ff)       LDA  #$ff
#0x101A: (60)          RTS  
end:
#0x101B: (a9 42)       LDA  #$42
#0x101D: (60)          RTS  
----- End of disassembly -----";

        let actual_output = output.join("\n");
        assert_eq!(actual_output, expected_output, "\nExpected:\n{}\n\nActual:\n{}\n", expected_output, actual_output);
    }

    #[test]
    fn test_disassemble_with_indirect_addressing() {
        let mut memory = Memory::new_with_ram();
        let mut symbols = Some(SymbolTable::new());
        
        // Write a program with indirect addressing modes
        memory.write(0x1000, &[
            0xb1, 0x88,             // LDA ($88),Y
            0xa1, 0x90,             // LDA ($90,X)
            0x81, 0x92,             // STA ($92,X)
            0x91, 0x94,             // STA ($94),Y
            0x60                    // RTS
        ]).unwrap();
        
        // Add symbols for zero page locations
        if let Some(symbols) = &mut symbols {
            symbols.add_symbol(0x0088, "PTR1".to_string());
            symbols.add_symbol(0x0090, "PTR2".to_string());
            symbols.add_symbol(0x0092, "PTR3".to_string());
            symbols.add_symbol(0x0094, "PTR4".to_string());
        }

        let disassembler = Disassembler::new(&memory, &mut symbols);
        let output = disassembler.disassemble_range(0x1000, 0x1008).unwrap();

        let expected_output = "\
---- Start of disassembly ----
#0x1000: (b1 88)       LDA  (PTR1),Y
#0x1002: (a1 90)       LDA  (PTR2,X)
#0x1004: (81 92)       STA  (PTR3,X)
#0x1006: (91 94)       STA  (PTR4),Y
#0x1008: (60)          RTS  
----- End of disassembly -----";

        let actual_output = output.join("\n");
        assert_eq!(actual_output, expected_output, "\nExpected:\n{}\n\nActual:\n{}\n", expected_output, actual_output);
    }
} 