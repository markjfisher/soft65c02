use std::path::{Path, PathBuf};
use std::collections::HashSet;
use anyhow::{Result, Context};
use serde::Deserialize;
use std::env;
use regex::Regex;
use std::any::Any;

/// Trait defining the interface for compiler-specific configurations
pub trait CompilerConfigTrait: std::fmt::Debug + Any {
    /// Merge another configuration of the same type into this one
    fn merge(&mut self, other: &dyn CompilerConfigTrait);
    /// Clone the configuration
    fn box_clone(&self) -> Box<dyn CompilerConfigTrait>;
    /// Convert to Any for downcasting
    fn as_any(&self) -> &dyn Any;
    /// Convert to mutable Any for downcasting
    fn as_any_mut(&mut self) -> &mut dyn Any;
}

impl Clone for Box<dyn CompilerConfigTrait> {
    fn clone(&self) -> Self {
        self.box_clone()
    }
}

#[derive(Debug, Deserialize, Clone, PartialEq)]
#[serde(rename_all = "lowercase")]
pub enum CompilerType {
    CC65,
}

/// Configuration structure that handles both raw loading and processed state
#[derive(Debug, Deserialize, Clone)]
pub struct Config {
    pub name: Option<String>,
    pub target: Option<String>,
    pub compiler: Option<CompilerType>,
    pub include_paths: Option<Vec<PathBuf>>,
    pub src_files: Option<Vec<PathBuf>>,
    pub test_script: Option<PathBuf>,
    pub configs: Option<Vec<PathBuf>>,
    #[serde(flatten)]
    raw_compiler_config: Option<serde_yaml::Value>,
    #[serde(skip)]
    pub compiler_config: Option<Box<dyn CompilerConfigTrait>>,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            name: None,
            target: None,
            compiler: None,
            include_paths: None,
            src_files: None,
            test_script: None,
            configs: None,
            raw_compiler_config: None,
            compiler_config: None,
        }
    }
}

/// CC65-specific compiler configuration
#[derive(Debug, Deserialize, Clone, Default)]
#[serde(default)]
pub struct CC65Config {
    pub config_file: Option<PathBuf>,
    pub asm_include_paths: Option<Vec<PathBuf>>,
}

impl CompilerConfigTrait for CC65Config {
    fn merge(&mut self, other: &dyn CompilerConfigTrait) {
        if let Some(other) = other.as_any().downcast_ref::<CC65Config>() {
            // For config_file, we want to keep the most specific one (last one wins)
            // Only update if other has a config file path
            if let Some(ref other_path) = other.config_file {
                self.config_file = Some(other_path.clone());
            }
            
            // For include paths, we want to combine them while preserving order and removing duplicates
            match (&mut self.asm_include_paths, &other.asm_include_paths) {
                (Some(self_paths), Some(other_paths)) => {
                    // Create a HashSet to track what we've already added
                    let mut seen = std::collections::HashSet::new();
                    let mut merged = Vec::new();
                    
                    // Add self paths first
                    for path in self_paths.iter() {
                        if seen.insert(path.clone()) {
                            merged.push(path.clone());
                        }
                    }
                    
                    // Add other paths
                    for path in other_paths.iter() {
                        if seen.insert(path.clone()) {
                            merged.push(path.clone());
                        }
                    }
                    
                    *self_paths = merged;
                }
                (None, Some(paths)) => {
                    self.asm_include_paths = Some(paths.clone());
                }
                _ => {}
            }
        }
    }

    fn box_clone(&self) -> Box<dyn CompilerConfigTrait> {
        Box::new(self.clone())
    }
    
    fn as_any(&self) -> &dyn Any {
        self
    }

    fn as_any_mut(&mut self) -> &mut dyn Any {
        self
    }
}

impl Config {
    pub fn load(path: &Path) -> Result<Self> {
        let mut loaded_paths = HashSet::new();
        Self::load_with_tracking(path, &mut loaded_paths)
    }

    fn load_with_tracking(path: &Path, loaded_paths: &mut HashSet<PathBuf>) -> Result<Self> {
        let canonical_path = path.canonicalize()
            .with_context(|| format!("Failed to canonicalize path: {}", path.display()))?;
        
        if !loaded_paths.insert(canonical_path.clone()) {
            return Err(anyhow::anyhow!("Circular dependency detected while loading config: {}", path.display()));
        }

        let mut config: Config = Self::load_yaml(path)?;
        let config_dir = path.parent().unwrap_or_else(|| Path::new(""));
        
        // Process compiler configuration first
        if let Some(CompilerType::CC65) = config.compiler {
            if let Some(ref raw_value) = config.raw_compiler_config {
                // Extract the inner compiler_config if it exists
                let config_value = if let Some(inner) = raw_value.get("compiler_config") {
                    inner
                } else {
                    raw_value
                };
                
                let mut cc65_config: CC65Config = serde_yaml::from_value(config_value.clone())
                    .with_context(|| "Failed to parse CC65 config")?;
                
                // Resolve config file path if present
                if let Some(cf) = cc65_config.config_file.take() {
                    // Normalize the path by removing . and .. components
                    let resolved_path = config_dir.join(cf).clean();
                    cc65_config.config_file = Some(resolved_path);
                }
                if let Some(paths) = &mut cc65_config.asm_include_paths {
                    // Normalize all include paths
                    *paths = paths.iter().map(|p| config_dir.join(p).clean()).collect();
                }
                
                config.compiler_config = Some(Box::new(cc65_config));
            }
        }

        // Resolve all paths relative to the config file's directory
        config.resolve_paths(config_dir);
        
        // Process included configs
        if let Some(config_paths) = config.configs.take() {
            for config_path in config_paths {
                let full_path = config_dir.join(&config_path).clean();
                
                if !full_path.exists() {
                    return Err(anyhow::anyhow!(
                        "Config file not found: {}. Paths are resolved relative to the config file directory: {}",
                        config_path.display(),
                        config_dir.display()
                    ));
                }
                
                let other_config = Self::load_with_tracking(&full_path, loaded_paths)
                    .with_context(|| format!("Failed to load config from {}", config_path.display()))?;
                
                config = config.merge(other_config);
            }
        }

        Ok(config)
    }

    fn resolve_paths(&mut self, base_dir: &Path) {
        if let Some(paths) = &mut self.include_paths {
            *paths = paths.iter().map(|p| base_dir.join(p).clean()).collect();
        }
        if let Some(paths) = &mut self.src_files {
            *paths = paths.iter().map(|p| base_dir.join(p).clean()).collect();
        }
        if let Some(script) = &mut self.test_script {
            *script = base_dir.join(script.clone()).clean();
        }
    }

    fn merge(self, other: Config) -> Config {
        // Merge compiler configurations if they exist
        let compiler_config = match (self.compiler_config, other.compiler_config) {
            (Some(mut self_cc), Some(other_cc)) => {
                self_cc.merge(&*other_cc);
                Some(self_cc)
            },
            (None, Some(cc)) => Some(cc),
            (Some(cc), None) => Some(cc),
            (None, None) => None,
        };

        Config {
            name: other.name.or(self.name),
            target: other.target.or(self.target),
            compiler: other.compiler.or(self.compiler),
            include_paths: match (self.include_paths, other.include_paths) {
                (Some(mut self_paths), Some(other_paths)) => {
                    self_paths.extend(other_paths);
                    Some(self_paths)
                }
                (Some(paths), None) | (None, Some(paths)) => Some(paths),
                (None, None) => None,
            },
            src_files: match (self.src_files, other.src_files) {
                (Some(mut self_files), Some(other_files)) => {
                    self_files.extend(other_files);
                    Some(self_files)
                }
                (Some(files), None) | (None, Some(files)) => Some(files),
                (None, None) => None,
            },
            test_script: other.test_script.or(self.test_script),
            configs: None, // Configs have already been processed
            raw_compiler_config: None, // Raw config has been processed into compiler_config
            compiler_config,
        }
    }

    fn load_yaml<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T> {
        let contents = std::fs::read_to_string(path)?;
        let contents_with_env = replace_env_vars(&contents)?;
        serde_yaml::from_str(&contents_with_env)
            .with_context(|| format!("Failed to parse YAML from {}", path.display()))
    }
}

fn replace_env_vars(content: &str) -> Result<String> {
    let re = Regex::new(r"\$\{([^}]+)\}").context("Failed to compile regex pattern")?;
    let mut modified_content = content.to_string();
    
    for capture in re.captures_iter(content) {
        let full_match = capture.get(0).unwrap().as_str();
        let var_name = capture.get(1).unwrap().as_str();
        let value = env::var(var_name)
            .with_context(|| format!("Environment variable '{}' not found", var_name))?;
        modified_content = modified_content.replace(full_match, &value);
    }
    
    Ok(modified_content)
}

// Helper trait for path normalization
trait PathClean {
    fn clean(&self) -> PathBuf;
}

impl PathClean for PathBuf {
    fn clean(&self) -> PathBuf {
        let mut components = Vec::new();
        for component in self.components() {
            match component {
                std::path::Component::ParentDir => {
                    if !components.is_empty() && components.last() != Some(&std::path::Component::ParentDir) {
                        components.pop();
                    } else {
                        components.push(component);
                    }
                },
                std::path::Component::CurDir => {},
                _ => components.push(component),
            }
        }
        components.iter().collect()
    }
}

impl PathClean for Path {
    fn clean(&self) -> PathBuf {
        self.to_path_buf().clean()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use tempfile::TempDir;

    #[test]
    fn test_replace_env_vars() {
        env::set_var("TEST_VAR", "test_value");
        env::set_var("ANOTHER_VAR", "another_value");

        let content = "prefix_${TEST_VAR}_${ANOTHER_VAR}_suffix";
        let result = replace_env_vars(content).unwrap();
        assert_eq!(result, "prefix_test_value_another_value_suffix");

        // Clean up
        env::remove_var("TEST_VAR");
        env::remove_var("ANOTHER_VAR");
    }

    #[test]
    fn test_missing_env_var_returns_error() {
        let content = "prefix_${NONEXISTENT_VAR}_suffix";
        let result = replace_env_vars(content);
        assert!(result.is_err());
        assert!(result.unwrap_err().to_string().contains("Environment variable 'NONEXISTENT_VAR' not found"));
    }

    #[test]
    fn test_load_config_with_env_vars() -> Result<()> {
        // Create a temporary directory for our test config
        let temp_dir = TempDir::new()?;
        let config_path = temp_dir.path().join("test_config.yaml");

        // Set up test environment variables
        env::set_var("TEST_NAME", "test_project");
        env::set_var("TEST_TARGET", "target_dir");

        // Create a test config file
        let config_content = r#"
name: ${TEST_NAME}
target: ${TEST_TARGET}
compiler: "cc65"
"#;
        fs::write(&config_path, config_content)?;

        // Load and verify the config
        let config: Config = Config::load(&config_path)?;
        
        assert_eq!(config.name, Some("test_project".to_string()));
        assert_eq!(config.target, Some("target_dir".to_string()));
        assert_eq!(config.compiler, Some(CompilerType::CC65));

        // Clean up
        env::remove_var("TEST_NAME");
        env::remove_var("TEST_TARGET");
        
        Ok(())
    }

    #[test]
    fn test_config_merge() -> Result<()> {
        let temp_dir = TempDir::new()?;
        
        // Create main config
        let main_config_path = temp_dir.path().join("main_config.yaml");
        env::set_var("MAIN_NAME", "main_project");
        let main_content = r#"
name: ${MAIN_NAME}
target: "main_target"
configs:
  - "sub_config.yaml"
"#;
        fs::write(&main_config_path, main_content)?;

        // Create sub config - this should override main config values
        let sub_config_path = temp_dir.path().join("sub_config.yaml");
        env::set_var("SUB_TARGET", "sub_target");
        let sub_content = r#"
compiler: "cc65"
target: ${SUB_TARGET}
"#;
        fs::write(&sub_config_path, sub_content)?;

        // Test from main config directory
        std::env::set_current_dir(temp_dir.path())?;
        
        let config = Config::load(&main_config_path)?;
        
        assert_eq!(config.name, Some("main_project".to_string()));
        assert_eq!(config.target, Some("sub_target".to_string())); // Sub config overrides main config
        assert_eq!(config.compiler, Some(CompilerType::CC65));     // Value from sub config wins

        // Clean up
        env::remove_var("MAIN_NAME");
        env::remove_var("SUB_TARGET");
        
        Ok(())
    }

    #[test]
    fn test_compiler_config_merge() -> Result<()> {
        let temp_dir = TempDir::new()?;
        
        // Create main config
        let main_config_path = temp_dir.path().join("main_config.yaml");
        let main_content = r#"
name: test_project
compiler: cc65
compiler_config:
  asm_include_paths:
    - "src"
configs:
  - "base_config.yaml"
"#;
        fs::write(&main_config_path, main_content)?;

        // Create base config
        let base_config_path = temp_dir.path().join("base_config.yaml");
        let base_content = r#"
compiler: cc65
compiler_config:
  config_file: "./config.cfg"
"#;
        fs::write(&base_config_path, base_content)?;

        // Test from main config directory
        std::env::set_current_dir(temp_dir.path())?;
        
        let config = Config::load(&main_config_path)?;
        
        // Get CC65-specific config
        let cc65_config = if let Some(compiler_config) = &config.compiler_config {
            compiler_config.as_any()
                .downcast_ref::<CC65Config>()
                .ok_or_else(|| anyhow::anyhow!("Invalid compiler configuration type"))?
        } else {
            return Err(anyhow::anyhow!("No compiler configuration found"));
        };

        // Verify both configs were merged with normalized paths
        let expected_config_path = temp_dir.path().join("config.cfg").clean();
        let expected_asm_path = temp_dir.path().join("src").clean();
        
        assert_eq!(cc65_config.config_file.as_ref().map(|p| p.to_path_buf()),
                  Some(expected_config_path));
        assert_eq!(cc65_config.asm_include_paths.as_ref().map(|p| &p[0]),
                  Some(&expected_asm_path));
        
        Ok(())
    }

    #[test]
    fn test_config_file_path_resolution() -> Result<()> {
        let temp_dir = TempDir::new()?;
        let base_dir = temp_dir.path().join("configs");
        fs::create_dir(&base_dir)?;
        
        // Create a config file in a subdirectory
        let config_path = base_dir.join("test_config.yaml");
        let config_content = r#"
name: test_project
compiler: cc65
compiler_config:
  config_file: "./linker.cfg"
"#;
        fs::write(&config_path, config_content)?;

        // Create the linker config file in the same directory
        fs::write(base_dir.join("linker.cfg"), "dummy content")?;

        // Load the config
        let config = Config::load(&config_path)?;
        
        // Get CC65-specific config
        let cc65_config = if let Some(compiler_config) = &config.compiler_config {
            compiler_config.as_any()
                .downcast_ref::<CC65Config>()
                .ok_or_else(|| anyhow::anyhow!("Invalid compiler configuration type"))?
        } else {
            return Err(anyhow::anyhow!("No compiler configuration found"));
        };

        // The config file path should be absolute and point to the correct location
        let expected_path = base_dir.join("linker.cfg");
        assert_eq!(cc65_config.config_file.as_ref().map(|p| p.canonicalize().unwrap()),
                  Some(expected_path.canonicalize()?));
        
        Ok(())
    }

    #[test]
    fn test_config_file_path_resolution_with_includes() -> Result<()> {
        let temp_dir = TempDir::new()?;
        let base_dir = temp_dir.path().join("configs");
        fs::create_dir(&base_dir)?;
        
        // Create the main config file
        let main_config_path = base_dir.join("main_config.yaml");
        let main_content = r#"
name: test_project
configs:
  - "sub/sub_config.yaml"
"#;
        fs::write(&main_config_path, main_content)?;

        // Create a subdirectory for the included config
        let sub_dir = base_dir.join("sub");
        fs::create_dir(&sub_dir)?;

        // Create the included config file
        let sub_config_path = sub_dir.join("sub_config.yaml");
        let sub_content = r#"
compiler: cc65
compiler_config:
  config_file: "./sub_linker.cfg"
"#;
        fs::write(&sub_config_path, sub_content)?;

        // Create the linker config file in the subdirectory
        fs::write(sub_dir.join("sub_linker.cfg"), "dummy content")?;

        // Load the config
        let config = Config::load(&main_config_path)?;
        
        // Get CC65-specific config
        let cc65_config = if let Some(compiler_config) = &config.compiler_config {
            compiler_config.as_any()
                .downcast_ref::<CC65Config>()
                .ok_or_else(|| anyhow::anyhow!("Invalid compiler configuration type"))?
        } else {
            return Err(anyhow::anyhow!("No compiler configuration found"));
        };

        // The config file path should be absolute and point to the correct location in the subdirectory
        let expected_path = sub_dir.join("sub_linker.cfg");
        assert_eq!(cc65_config.config_file.as_ref().map(|p| p.canonicalize().unwrap()),
                  Some(expected_path.canonicalize()?));
        
        Ok(())
    }
} 