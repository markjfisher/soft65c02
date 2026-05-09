//! Serialized emulator session for MCP / disk persistence ([`crate::ExecutorSession`]).
//! Format version must stay compatible with [`SESSION_FORMAT_VERSION`].

use serde::{Deserialize, Serialize};
use soft65c02_lib::{MemoryRegionExport, RegisterSnapshot};

pub const SESSION_FORMAT_VERSION: u32 = 1;

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct SessionCheckpoint {
    pub format_version: u32,
    pub registers: RegisterSnapshot,
    pub memory_regions: Vec<MemoryRegionExport>,
    pub symbols: Vec<(String, u16)>,
    pub round_failed: bool,
    pub had_terminated_run: bool,
    pub ignore_parse_error: bool,
    pub stop_on_failed_assertion: bool,
    pub allow_commands_after_terminated_run: bool,
}

pub fn encode_session_checkpoint(c: &SessionCheckpoint) -> crate::AppResult<Vec<u8>> {
    Ok(bincode::serialize(c)?)
}

pub fn decode_session_checkpoint(bytes: &[u8]) -> crate::AppResult<SessionCheckpoint> {
    Ok(bincode::deserialize(bytes)?)
}

#[cfg(test)]
mod tests {
    use super::*;
    use soft65c02_lib::{AddressableIO, Memory};

    #[test]
    fn checkpoint_encode_roundtrip() {
        let mut m = Memory::new_with_ram();
        m.write(0x0200, &[0xde, 0xad]).unwrap();
        let cp = SessionCheckpoint {
            format_version: SESSION_FORMAT_VERSION,
            registers: RegisterSnapshot {
                accumulator: 1,
                register_x: 2,
                register_y: 3,
                status_register: 0x30,
                command_pointer: 0x0200,
                stack_pointer: 0xfc,
                cycle_count: 42,
            },
            memory_regions: m.export_regions(),
            symbols: vec![("entry".into(), 0x0200)],
            round_failed: false,
            had_terminated_run: true,
            ignore_parse_error: false,
            stop_on_failed_assertion: false,
            allow_commands_after_terminated_run: true,
        };
        let bytes = encode_session_checkpoint(&cp).unwrap();
        let cp2 = decode_session_checkpoint(&bytes).unwrap();
        assert_eq!(cp, cp2);
    }
}
