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
    dry_run: bool,
}

impl TestRunner {
    pub fn from_yaml(test_yaml: &Path, build_dir: Option<PathBuf>, verbose: bool, dry_run: bool) -> Result<Self> {
        // Determine build directory - command line takes precedence over environment variable
        let work_dir = build_dir.or_else(|| env::var("SOFT65C02_BUILD_DIR").ok().map(PathBuf::from))
            .ok_or_else(|| anyhow::anyhow!("Build directory must be specified either via --build-dir option or SOFT65C02_BUILD_DIR environment variable"))?;

        if verbose || dry_run {
            println!("Loading test config from: {:?}", test_yaml);
            println!("Build directory: {:?}", work_dir);
        }
        
        // Load test configuration
        let config = Config::load(test_yaml)
            .with_context(|| format!("Failed to load test config from {}", test_yaml.display()))?;
        
        // Get compiler from config
        let compiler_type = config.compiler
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("No compiler specified in config"))?;

        // Create and clean the build directory
        if !dry_run {
            if work_dir.exists() {
                std::fs::remove_dir_all(&work_dir)?;
            }
            std::fs::create_dir_all(&work_dir)?;
        } else {
            println!("[DRY RUN] Would remove and recreate build directory: {:?}", work_dir);
        }

        // Create compiler implementation
        let compiler = create_compiler(compiler_type, &config, verbose, dry_run)?;
        
        Ok(Self {
            config,
            work_dir,
            compiler,
            verbose,
            dry_run,
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
            // Create path mapping for the already canonicalized paths
            let path_mapping = self.compiler.create_output_path_mapping(src_files);

            // Compile each source file using the mapping
            for src in src_files {
                let obj = self.compiler.compile_source(src, &self.work_dir, &path_mapping)?;
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

        if self.verbose || self.dry_run {
            self.debug_command(&cmd);
        }
        
        if self.dry_run {
            println!("[DRY RUN] Would execute soft65c02_tester");
            return Ok(());
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