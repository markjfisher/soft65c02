/// Format a memory region as a hex dump with both hex and ASCII representation
pub fn format_hex_dump(addr: usize, bytes: &[u8]) -> String {
    let mut result = String::new();
    for chunk_start in (0..bytes.len()).step_by(16) {
        let chunk_end = std::cmp::min(chunk_start + 16, bytes.len());
        let chunk = &bytes[chunk_start..chunk_end];
        
        // Add address
        result.push_str(&format!("{:04X} : ", addr + chunk_start));
        
        // Add hex bytes
        for &byte in chunk {
            result.push_str(&format!("{:02X} ", byte));
        }
        
        // Pad with spaces if less than 16 bytes
        for _ in chunk.len()..16 {
            result.push_str("   ");
        }
        
        // Add ASCII representation
        result.push_str("| ");
        for &byte in chunk {
            let ch = if byte >= 0x20 && byte <= 0x7E {
                byte as char
            } else {
                '.'
            };
            result.push(ch);
        }
        
        // Add newline if not the last line
        if chunk_end < bytes.len() {
            result.push('\n');
        }
    }
    result
} 