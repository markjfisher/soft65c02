mod commands;
mod displayer;
mod executor;
mod session_checkpoint;
mod pest_parser;
mod until_condition;
pub mod atari_binary;
pub mod apple_single;
pub mod symbols;
pub mod disassembler;
pub mod utils;

pub use commands::*;
pub use displayer::*;
pub use executor::*;
pub use session_checkpoint::{
    decode_session_checkpoint, encode_session_checkpoint, SessionCheckpoint, SESSION_FORMAT_VERSION,
};
pub use pest_parser::CliCommandParser;
pub use symbols::SymbolTable;
pub use disassembler::Disassembler;

pub type AppResult<T> = anyhow::Result<T>;
