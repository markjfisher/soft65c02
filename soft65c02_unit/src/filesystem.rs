use std::path::Path;
use std::fs;

// This is an abstraction allowing us to perform filesystem operations in tests without actually
// having the side effects of actually making those real calls, so we can test our functions without the side effects.

/// Trait for filesystem operations
pub trait FileSystem {
    fn create_dir_all(&self, path: &Path) -> Result<(), String>;
}

/// Default filesystem implementation that uses std::fs
pub struct DefaultFileSystem;

impl FileSystem for DefaultFileSystem {
    fn create_dir_all(&self, path: &Path) -> Result<(), String> {
        fs::create_dir_all(path)
            .map_err(|e| format!("Failed to create directory {}: {}", path.display(), e))
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use std::cell::RefCell;
    use std::rc::Rc;
    use std::path::{Path, PathBuf};

    /// Mock filesystem that records operations and returns predefined results
    pub struct MockFileSystem {
        created_dirs: Rc<RefCell<Vec<PathBuf>>>,
        results: Vec<Result<(), String>>,
    }

    impl MockFileSystem {
        pub fn new(results: Vec<Result<(), String>>) -> Self {
            Self {
                created_dirs: Rc::new(RefCell::new(Vec::new())),
                results,
            }
        }

        pub fn get_created_dirs(&self) -> Vec<PathBuf> {
            self.created_dirs.borrow().clone()
        }
    }

    impl FileSystem for MockFileSystem {
        fn create_dir_all(&self, path: &Path) -> Result<(), String> {
            self.created_dirs.borrow_mut().push(path.to_path_buf());
            self.results.get(self.created_dirs.borrow().len() - 1)
                .cloned()
                .unwrap_or(Ok(()))
        }
    }

    #[test]
    fn test_mock_filesystem() {
        let mock = MockFileSystem::new(vec![
            Ok(()),
            Err("mock error".to_string()),
            Ok(()),
        ]);

        let path1 = PathBuf::from("test/dir1");
        let path2 = PathBuf::from("test/dir2");
        let path3 = PathBuf::from("test/dir3");

        assert!(mock.create_dir_all(&path1).is_ok());
        assert!(mock.create_dir_all(&path2).is_err());
        assert!(mock.create_dir_all(&path3).is_ok());

        let created_dirs = mock.get_created_dirs();
        assert_eq!(created_dirs.len(), 3);
        assert_eq!(created_dirs[0], path1);
        assert_eq!(created_dirs[1], path2);
        assert_eq!(created_dirs[2], path3);
    }

} 