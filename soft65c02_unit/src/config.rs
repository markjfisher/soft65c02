use std::path::{Path, PathBuf};
use std::collections::HashSet;
use anyhow::{Result, Context};
use serde::Deserialize;
use std::env;
use regex::Regex;

#[derive(Debug, Deserialize)]
pub struct Config {
    pub name: Option<String>,
    pub target: Option<String>,
    pub compiler: Option<String>,
    pub include_paths: Option<Vec<PathBuf>>,
    pub asm_include_paths: Option<Vec<PathBuf>>,
    pub config_file: Option<PathBuf>,
    pub configs: Option<Vec<PathBuf>>,
    pub test_start: Option<PathBuf>,
    pub src_files: Option<Vec<PathBuf>>,
    pub test_script: Option<PathBuf>,
    pub sources: Option<Vec<PathBuf>>,
}

impl Config {
    pub fn load(path: &Path) -> Result<Self> {
        let mut loaded_paths = HashSet::new();
        Self::load_with_tracking(path, &mut loaded_paths)
    }

    fn load_with_tracking(path: &Path, loaded_paths: &mut HashSet<PathBuf>) -> Result<Self> {
        // Convert to canonical path to handle relative paths correctly
        let canonical_path = path.canonicalize()
            .with_context(|| format!("Failed to canonicalize path: {}", path.display()))?;
        
        // Check if we've already loaded this config
        if !loaded_paths.insert(canonical_path.clone()) {
            return Err(anyhow::anyhow!("Circular dependency detected while loading config: {}", path.display()));
        }

        // Load the current config file
        let config: Config = load_yaml(path)?;
        
        // Load and merge any referenced configs
        if let Some(config_paths) = &config.configs {
            // Clone the paths to avoid borrowing config
            let paths_to_process: Vec<PathBuf> = config_paths.clone();
            let mut merged_config = config;
            
            for config_path in paths_to_process {
                // Use paths relative to current working directory
                let full_path = std::env::current_dir()?.join(&config_path);
                let other_config = Self::load_with_tracking(&full_path, loaded_paths)
                    .with_context(|| format!("Failed to load config from {}", config_path.display()))?;
                merged_config = merged_config.merge(other_config);
            }
            
            Ok(merged_config)
        } else {
            Ok(config)
        }
    }

    fn merge(self, other: Config) -> Config {
        Config {
            // Take non-None values from self, fall back to other
            name: self.name.or(other.name),
            target: self.target.or(other.target),
            compiler: self.compiler.or(other.compiler),
            config_file: self.config_file.or(other.config_file),
            test_start: self.test_start.or(other.test_start),
            test_script: self.test_script.or(other.test_script),
            
            // Merge Vec fields if both exist
            include_paths: match (self.include_paths, other.include_paths) {
                (Some(mut self_paths), Some(other_paths)) => {
                    self_paths.extend(other_paths);
                    Some(self_paths)
                }
                (Some(paths), None) | (None, Some(paths)) => Some(paths),
                (None, None) => None,
            },
            
            asm_include_paths: match (self.asm_include_paths, other.asm_include_paths) {
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
            
            sources: match (self.sources, other.sources) {
                (Some(mut self_sources), Some(other_sources)) => {
                    self_sources.extend(other_sources);
                    Some(self_sources)
                }
                (Some(sources), None) | (None, Some(sources)) => Some(sources),
                (None, None) => None,
            },
            
            // Clear configs as they've been processed
            configs: None,
        }
    }
}

pub fn load_yaml<T: for<'de> Deserialize<'de>>(path: &Path) -> Result<T> {
    let contents = std::fs::read_to_string(path)?;
    let contents_with_env = replace_env_vars(&contents)?;
    Ok(serde_yaml::from_str(&contents_with_env)?)
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
compiler: "gcc"
"#;
        fs::write(&config_path, config_content)?;

        // Load and verify the config
        let config: Config = Config::load(&config_path)?;
        
        assert_eq!(config.name, Some("test_project".to_string()));
        assert_eq!(config.target, Some("target_dir".to_string()));
        assert_eq!(config.compiler, Some("gcc".to_string()));

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

        // Create sub config
        let sub_config_path = temp_dir.path().join("sub_config.yaml");
        env::set_var("SUB_TARGET", "sub_target");
        let sub_content = r#"
compiler: "gcc"
target: ${SUB_TARGET}
"#;
        fs::write(&sub_config_path, sub_content)?;

        // Test from main config directory
        std::env::set_current_dir(temp_dir.path())?;
        
        let config = Config::load(&main_config_path)?;
        assert_eq!(config.name, Some("main_project".to_string()));
        assert_eq!(config.target, Some("main_target".to_string())); // Main config takes precedence
        assert_eq!(config.compiler, Some("gcc".to_string()));

        // Clean up
        env::remove_var("MAIN_NAME");
        env::remove_var("SUB_TARGET");
        
        Ok(())
    }
} 