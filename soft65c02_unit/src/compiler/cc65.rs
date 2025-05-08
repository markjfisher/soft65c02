use std::path::{Path, PathBuf};
use anyhow::Result;

use super::Compiler;
use crate::config::Config;
use crate::executor::{Executor, CommandExecutor};
use crate::filesystem::{FileSystem, DefaultFileSystem};

pub struct CC65Compiler {
    target: String,
    include_paths: Vec<PathBuf>,
    asm_include_paths: Vec<PathBuf>,
    config_file: PathBuf,
    verbose: bool,
    executor: Box<dyn Executor>,
    fs: Box<dyn FileSystem>,
}

impl CC65Compiler {
    pub fn new(config: &Config, verbose: bool) -> Result<Self> {
        // Verify we have the required configuration
        let target = config.target
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("No target specified in config"))?
            .clone();
            
        let config_file = config.config_file
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("No config file specified in config"))?
            .clone();

        Ok(Self {
            target,
            include_paths: config.include_paths.clone().unwrap_or_default(),
            asm_include_paths: config.asm_include_paths.clone().unwrap_or_default(),
            config_file,
            verbose,
            executor: Box::new(CommandExecutor::new("cl65")),
            fs: Box::new(DefaultFileSystem),
        })
    }

    /// Create a new compiler with custom executor and filesystem (mainly for testing)
    #[cfg(test)]
    pub fn with_mock_impls(
        config: &Config,
        verbose: bool,
        executor: Box<dyn Executor>,
        fs: Box<dyn FileSystem>,
    ) -> Result<Self> {
        let target = config.target
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("No target specified in config"))?
            .clone();
            
        let config_file = config.config_file
            .as_ref()
            .ok_or_else(|| anyhow::anyhow!("No config file specified in config"))?
            .clone();

        Ok(Self {
            target,
            include_paths: config.include_paths.clone().unwrap_or_default(),
            asm_include_paths: config.asm_include_paths.clone().unwrap_or_default(),
            config_file,
            verbose,
            executor,
            fs,
        })
    }

    fn debug_command(&self, args: &[String]) {
        if self.verbose {
            println!("Command: cl65 {}", args.join(" "));
        }
    }

    /// Creates a directory structure in the work_dir that matches the source file's path
    fn create_output_dirs(&self, source: &Path, work_dir: &Path) -> Result<PathBuf> {
        // Get the parent directory of the source file, if any
        let parent = source.parent().unwrap_or_else(|| Path::new(""));
        let output_dir = work_dir.join(parent);

        // Create the directory structure
        self.fs.create_dir_all(&output_dir)
            .map_err(|e| anyhow::anyhow!("Failed to create output directory: {}", e))?;

        Ok(output_dir)
    }

    fn generate_compile_args(&self, source: &Path, obj_file: &Path, dep_file: &Path, lst_file: &Path) -> Vec<String> {
        let mut args = Vec::new();
        
        // Target platform must come first
        args.extend(["-t".to_string(), self.target.clone()]);
        
        // Compile only
        args.push("-c".to_string());
        
        // Dependency file
        args.extend([
            "--create-dep".to_string(),
            dep_file.to_string_lossy().to_string()
        ]);
        
        // C include paths in order
        for path in &self.include_paths {
            args.extend([
                "--include-dir".to_string(),
                path.to_string_lossy().to_string()
            ]);
        }

        // Assembly include paths in order
        for path in &self.asm_include_paths {
            args.extend([
                "--asm-include-dir".to_string(),
                path.to_string_lossy().to_string()
            ]);
        }
        
        // Listing file
        args.extend([
            "--listing".to_string(),
            lst_file.to_string_lossy().to_string()
        ]);
        
        // Output file must come before input
        args.extend([
            "-o".to_string(),
            obj_file.to_string_lossy().to_string()
        ]);
        
        // Input source must be last
        args.push(source.to_string_lossy().to_string());

        args
    }

    fn generate_link_args(&self, objects: &[PathBuf], output: &Path, map_file: &Path, lbl_file: &Path) -> Vec<String> {
        let mut args = Vec::new();
        
        // Target platform must come first
        args.extend(["-t".to_string(), self.target.clone()]);
        
        // Linker config
        args.extend([
            "-C".to_string(),
            self.config_file.to_string_lossy().to_string()
        ]);
        
        // Map and label files
        args.extend([
            "--mapfile".to_string(),
            map_file.to_string_lossy().to_string(),
            "-Ln".to_string(),
            lbl_file.to_string_lossy().to_string()
        ]);
        
        // Output binary must come before inputs
        args.extend([
            "-o".to_string(),
            output.to_string_lossy().to_string()
        ]);
        
        // Input objects must be last, in order
        for obj in objects {
            args.push(obj.to_string_lossy().to_string());
        }

        args
    }

    /// Execute cl65 with the given arguments
    fn execute_cl65(&self, args: &[String]) -> Result<(), String> {
        self.debug_command(args);
        self.executor.execute(args)
    }
}

impl Compiler for CC65Compiler {
    fn compile_source(&self, source: &Path, work_dir: &Path) -> Result<PathBuf> {
        // Create output directory structure matching source path
        let output_dir = self.create_output_dirs(source, work_dir)?;
        
        let obj_name = source.file_stem().unwrap();
        let obj_file = output_dir.join(obj_name).with_extension("o");
        let dep_file = output_dir.join(obj_name).with_extension("d");
        let lst_file = output_dir.join(obj_name).with_extension("lst");
        
        let args = self.generate_compile_args(source, &obj_file, &dep_file, &lst_file);
        self.execute_cl65(&args)
            .map_err(|e| anyhow::anyhow!("Failed to compile {}: {}", source.display(), e))?;

        Ok(obj_file)
    }

    fn link_objects(&self, objects: &[PathBuf], output: &Path, work_dir: &Path) -> Result<()> {
        let map_file = work_dir.join("app.map");
        let lbl_file = work_dir.join("app.lbl");
        
        let args = self.generate_link_args(objects, output, &map_file, &lbl_file);
        self.execute_cl65(&args)
            .map_err(|e| anyhow::anyhow!("Failed to link objects: {}", e))
    }

    fn get_symbols_path(&self, work_dir: &Path) -> PathBuf {
        work_dir.join("app.lbl")
    }

    fn is_verbose(&self) -> bool {
        self.verbose
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::executor::tests::MockExecutor;
    use crate::filesystem::tests::MockFileSystem;
    use crate::config::CompilerType;

    fn create_test_config() -> Config {
        let mut config = Config::default();
        config.target = Some("nes".to_string());
        config.compiler = Some(CompilerType::CC65);
        config.config_file = Some(PathBuf::from("test.cfg"));
        config.asm_include_paths = Some(vec![
            PathBuf::from("asm1"),
            PathBuf::from("asm2"),
        ]);
        config.include_paths = Some(vec![
            PathBuf::from("include1"),
            PathBuf::from("include2"),
        ]);
        config
    }

    fn create_test_compiler() -> CC65Compiler {
        CC65Compiler::new(&create_test_config(), true).unwrap()
    }

    #[test]
    fn test_compile_args_generation() {
        let compiler = create_test_compiler();
        let source = Path::new("src/test.c");
        let obj_file = Path::new("build/test.o");
        let dep_file = Path::new("build/test.d");
        let lst_file = Path::new("build/test.lst");

        let args = compiler.generate_compile_args(source, obj_file, dep_file, lst_file);

        // Define the expected order of arguments
        let expected_args = vec![
            "-t", "nes",           // Target platform must come first
            "-c",                  // Compile only
            "--create-dep", "build/test.d",  // Dependency file
            "--include-dir", "include1",     // C include paths in order
            "--include-dir", "include2",
            "--asm-include-dir", "asm1",     // ASM include paths in order
            "--asm-include-dir", "asm2",
            "--listing", "build/test.lst",   // Listing file
            "-o", "build/test.o",           // Output file must come before input
            "src/test.c",                   // Input file must be last
        ];

        // Convert expected args to String for comparison
        let expected: Vec<String> = expected_args.into_iter().map(String::from).collect();
        assert_eq!(args, expected, "Arguments are not in the expected order");
    }

    #[test]
    fn test_link_args_generation() {
        let compiler = create_test_compiler();
        let objects = vec![
            PathBuf::from("build/test1.o"),
            PathBuf::from("build/test2.o"),
        ];
        let output = Path::new("output/game.nes");
        let map_file = Path::new("output/app.map");
        let lbl_file = Path::new("output/app.lbl");

        let args = compiler.generate_link_args(&objects, output, map_file, lbl_file);

        // Define the expected order of arguments
        let expected_args = vec![
            "-t", "nes",           // Target platform must come first
            "-C", "test.cfg",      // Linker configuration
            "--mapfile", "output/app.map",  // Map file
            "-Ln", "output/app.lbl",       // Label file
            "-o", "output/game.nes",       // Output file must come before inputs
            "build/test1.o",              // Object files must be last, in order
            "build/test2.o",
        ];

        // Convert expected args to String for comparison
        let expected: Vec<String> = expected_args.into_iter().map(String::from).collect();
        assert_eq!(args, expected, "Arguments are not in the expected order");
    }

    #[test]
    fn test_compile_source_with_mocks() {
        let mock_executor = Box::new(MockExecutor::new(vec![Ok(())]));
        let mock_fs = Box::new(MockFileSystem::new(vec![Ok(())]));
        
        let compiler = CC65Compiler::with_mock_impls(
            &create_test_config(),
            true,
            mock_executor,
            mock_fs
        ).unwrap();
        
        let source = Path::new("src/test.c");
        let work_dir = Path::new("build");
        
        let result = compiler.compile_source(source, work_dir);
        assert!(result.is_ok());
    }

    #[test]
    fn test_filesystem_failure() {
        let mock_executor = Box::new(MockExecutor::new(vec![Ok(())]));
        let mock_fs = Box::new(MockFileSystem::new(vec![
            Err("Mock filesystem error".to_string())
        ]));
        
        let compiler = CC65Compiler::with_mock_impls(
            &create_test_config(),
            true,
            mock_executor,
            mock_fs
        ).unwrap();
        
        let source = Path::new("src/test.c");
        let work_dir = Path::new("build");
        
        let result = compiler.compile_source(source, work_dir);
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("Mock filesystem error"));
    }

    #[test]
    fn test_compile_failure() {
        let mock_executor = Box::new(MockExecutor::new(vec![
            Err("Mock compilation error".to_string())
        ]));
        let mock_fs = Box::new(MockFileSystem::new(vec![Ok(())]));
        
        let compiler = CC65Compiler::with_mock_impls(
            &create_test_config(),
            true,
            mock_executor,
            mock_fs
        ).unwrap();
        
        let source = Path::new("src/test.c");
        let work_dir = Path::new("build");
        
        let result = compiler.compile_source(source, work_dir);
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("Mock compilation error"));
    }
} 