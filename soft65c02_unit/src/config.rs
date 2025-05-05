use std::path::{Path, PathBuf};
use std::collections::HashSet;
use anyhow::{Result, Context};
use serde::Deserialize;

#[derive(Debug, Deserialize)]
pub struct Config {
    pub name: Option<String>,
    pub target: Option<String>,
    pub compiler: Option<String>,
    pub include_paths: Option<Vec<PathBuf>>,
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
    Ok(serde_yaml::from_str(&contents)?)
} 