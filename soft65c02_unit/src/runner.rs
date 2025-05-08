use std::path::{Path, PathBuf};
use anyhow::{Result, Context};
use std::process::Command;
use std::env;

use crate::compiler::{Compiler, create_compiler};
use crate::config::Config;

pub struct TestRunner {
    config: Config,
    work_dir: PathBuf,
    compiler: Box<dyn Compiler>,
    verbose: bool,
}

impl TestRunner {
    pub fn from_yaml(test_yaml: &Path, verbose: bool) -> Result<Self> {
        if verbose {
            println!("Current working directory: {:?}", std::env::current_dir()?);
            println!("Loading test config from: {:?}", test_yaml);
        }
        
        // Load test configuration
        let config = Config::load(test_yaml)
            .with_context(|| format!("Failed to load test config from {}", test_yaml.display()))?;
        
        // Get compiler from config
        let compiler_type = config.compiler
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("No compiler specified in config"))?;
        
        // Find workspace root
        let mut workspace_root = std::env::current_dir()?;
        while !workspace_root.join("Cargo.toml").exists() || 
              !std::fs::read_to_string(workspace_root.join("Cargo.toml"))?.contains("[workspace]") {
            workspace_root = workspace_root.parent()
                .ok_or_else(|| anyhow::anyhow!("Could not find workspace root"))?
                .to_path_buf();
        }

        // Create and clean the build directory
        let work_dir = workspace_root.join("build").join("test-output");
        if work_dir.exists() {
            std::fs::remove_dir_all(&work_dir)?;
        }
        std::fs::create_dir_all(&work_dir)?;
        
        if verbose {
            println!("Working directory: {:?}", work_dir);
        }

        // Create compiler implementation
        let compiler = create_compiler(compiler_type, &config, verbose)?;
        
        Ok(Self {
            config,
            work_dir,
            compiler,
            verbose,
        })
    }

    pub fn run(self) -> Result<()> {
        let (binary_path, symbols_path) = self.compile()?;
        self.run_tests(&binary_path, Some(&symbols_path))?;
        Ok(())
    }

    fn compile(&self) -> Result<(PathBuf, PathBuf)> {
        let mut object_files = Vec::new();
        
        // Compile all source files
        if let Some(src_files) = &self.config.src_files {
            for src in src_files {
                let obj = self.compiler.compile_source(src, &self.work_dir)?;
                object_files.push(obj);
            }
        }

        // Link everything together
        let binary_path = self.work_dir.join("app.bin");
        let symbols_path = self.compiler.get_symbols_path(&self.work_dir);
        
        self.compiler.link_objects(&object_files, &binary_path, &self.work_dir)?;

        Ok((binary_path, symbols_path))
    }

    fn run_tests(&self, binary_path: &Path, symbols_path: Option<&Path>) -> Result<()> {
        // Set up environment variables for the test script
        env::set_var("BUILD_DIR", &self.work_dir);
        env::set_var("BINARY_PATH", binary_path);
        if let Some(symbols) = symbols_path {
            env::set_var("SYMBOLS_PATH", symbols);
        }
        
        // Run the tester directly, assuming it's in the PATH
        let mut cmd = Command::new("soft65c02_tester");
        
        if self.verbose {
            cmd.arg("-v");
        }

        if let Some(test_script) = &self.config.test_script {
            cmd.arg("-i").arg(test_script);
        } else {
            anyhow::bail!("No test script specified in config");
        }

        if self.verbose {
            self.debug_command(&cmd);
        }
        
        let output = cmd.output()
            .with_context(|| "Failed to execute soft65c02_tester")?;

        // Print stdout for visibility
        println!("{}", String::from_utf8_lossy(&output.stdout));

        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            anyhow::bail!("Tests failed:\nExit code: {}\nError output:\n{}", 
                output.status.code().unwrap_or(-1),
                stderr);
        }

        Ok(())
    }

    fn debug_command(&self, cmd: &Command) {
        println!("Executing: {:?}", cmd);
    }
} 