use std::path::{Path, PathBuf};
use anyhow::{Result, Context};
use std::process::Command;

use super::Compiler;
use crate::config::Config;

pub struct CC65Compiler {
    target: String,
    include_paths: Vec<PathBuf>,
    config_file: PathBuf,
    verbose: bool,
}

impl CC65Compiler {
    pub fn new(config: &Config, verbose: bool) -> Result<Self> {
        Ok(Self {
            target: config.target
                .as_ref()
                .ok_or_else(|| anyhow::anyhow!("No target specified in config"))?
                .clone(),
            include_paths: config.include_paths
                .clone()
                .unwrap_or_default(),
            config_file: config.config_file
                .as_ref()
                .ok_or_else(|| anyhow::anyhow!("No config file specified in config"))?
                .clone(),
            verbose,
        })
    }

    fn debug_command(&self, cmd: &Command) {
        if self.verbose {
            println!("Executing: {:?}", cmd);
        }
    }
}

impl Compiler for CC65Compiler {
    fn compile_source(&self, source: &Path, work_dir: &Path) -> Result<PathBuf> {
        let obj_name = source.file_stem().unwrap();
        let obj_file = work_dir.join(obj_name).with_extension("o");
        let dep_file = work_dir.join(obj_name).with_extension("d");
        let lst_file = work_dir.join(obj_name).with_extension("lst");
        
        let mut cmd = Command::new("cl65");
        
        // Basic options
        cmd.arg("-t").arg(&self.target)
           .arg("-c");
        
        // Dependency file
        cmd.arg("--create-dep").arg(&dep_file);
        
        // Include paths - use --asm-include-dir for assembly files
        for path in &self.include_paths {
            cmd.arg("--asm-include-dir").arg(path);
        }
        
        // Listing file
        cmd.arg("--listing").arg(&lst_file);
        
        // Output object file and input source
        cmd.arg("-o").arg(&obj_file)
           .arg(source);

        self.debug_command(&cmd);
        let output = cmd.output()
            .with_context(|| format!("Failed to execute cl65 for {}", source.display()))?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            anyhow::bail!("Failed to compile {}: {}", source.display(), stderr);
        }

        Ok(obj_file)
    }

    fn link_objects(&self, objects: &[PathBuf], output: &Path, work_dir: &Path) -> Result<()> {
        let mut cmd = Command::new("cl65");
        
        // Basic options
        cmd.arg("-t").arg(&self.target);
        
        // Linker config
        cmd.arg("-C").arg(&self.config_file);
        
        // Generate map and label files
        let map_file = work_dir.join("app.map");
        let lbl_file = work_dir.join("app.lbl");
        cmd.arg("--mapfile").arg(&map_file)
           .arg("-Ln").arg(&lbl_file);
        
        // Output binary and input objects
        cmd.arg("-o").arg(output)
           .args(objects);

        self.debug_command(&cmd);
        let output = cmd.output()
            .context("Failed to execute cl65 linker")?;

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            anyhow::bail!("Failed to link objects: {}", stderr);
        }

        Ok(())
    }

    fn get_symbols_path(&self, work_dir: &Path) -> PathBuf {
        work_dir.join("app.lbl")
    }

    fn is_verbose(&self) -> bool {
        self.verbose
    }
} 