use std::path::{Path, PathBuf};
use anyhow::Result;

use crate::config::Config;

pub mod cc65;

pub trait Compiler {
    fn compile_source(&self, source: &Path, work_dir: &Path) -> Result<PathBuf>;
    fn link_objects(&self, objects: &[PathBuf], output: &Path, work_dir: &Path) -> Result<()>;
    fn get_symbols_path(&self, work_dir: &Path) -> PathBuf;
    fn is_verbose(&self) -> bool;
}

pub fn create_compiler(compiler_type: &str, config: &Config, verbose: bool) -> Result<Box<dyn Compiler>> {
    match compiler_type {
        "cc65" => Ok(Box::new(cc65::CC65Compiler::new(config, verbose)?)),
        _ => anyhow::bail!("Unsupported compiler type: {}", compiler_type),
    }
} 