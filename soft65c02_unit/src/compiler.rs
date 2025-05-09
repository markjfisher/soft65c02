use std::path::{Path, PathBuf};
use std::collections::HashMap;
use anyhow::Result;

use crate::config::{Config, CompilerType};

pub mod cc65;

pub trait Compiler {
    fn create_output_path_mapping(&self, sources: &[PathBuf]) -> HashMap<PathBuf, PathBuf>;
    fn compile_source(&self, source: &Path, work_dir: &Path, path_mapping: &HashMap<PathBuf, PathBuf>) -> Result<PathBuf>;
    fn link_objects(&self, objects: &[PathBuf], output: &Path, work_dir: &Path) -> Result<()>;
    fn get_symbols_path(&self, work_dir: &Path) -> PathBuf;
}

pub fn create_compiler(compiler_type: &CompilerType, config: &Config, verbose: bool, dry_run: bool) -> Result<Box<dyn Compiler>> {
    match compiler_type {
        CompilerType::CC65 => Ok(Box::new(cc65::CC65Compiler::new(config, verbose, dry_run)?)),
    }
} 