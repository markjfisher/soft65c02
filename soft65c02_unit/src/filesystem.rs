use std::path::{Path, PathBuf};
use std::fs;

// This is an abstraction allowing us to perform filesystem operations in tests without actually
// having the side effects of actually making those real calls, so we can test our functions without the side effects.

/// Trait for filesystem operations
pub trait FileSystem {
    fn create_dir_all(&self, path: &Path) -> Result<(), String>;
    fn canonicalize(&self, path: &Path) -> Result<PathBuf, String>;
}

/// Default filesystem implementation that uses std::fs
pub struct DefaultFileSystem;

impl FileSystem for DefaultFileSystem {
    fn create_dir_all(&self, path: &Path) -> Result<(), String> {
        fs::create_dir_all(path)
            .map_err(|e| format!("Failed to create directory {}: {}", path.display(), e))
    }

    fn canonicalize(&self, path: &Path) -> Result<PathBuf, String> {
        fs::canonicalize(path)
            .map_err(|e| format!("Failed to canonicalize path {}: {}", path.display(), e))
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
        canonicalized_paths: Rc<RefCell<Vec<PathBuf>>>,
        dir_results: Vec<Result<(), String>>,
        canonicalize_results: Vec<Result<PathBuf, String>>,
    }

    impl MockFileSystem {
        pub fn new(dir_results: Vec<Result<(), String>>, canonicalize_results: Vec<Result<PathBuf, String>>) -> Self {
            Self {
                created_dirs: Rc::new(RefCell::new(Vec::new())),
                canonicalized_paths: Rc::new(RefCell::new(Vec::new())),
                dir_results: dir_results,
                canonicalize_results,
            }
        }

        pub fn get_created_dirs(&self) -> Vec<PathBuf> {
            self.created_dirs.borrow().clone()
        }

        pub fn get_canonicalized_paths(&self) -> Vec<PathBuf> {
            self.canonicalized_paths.borrow().clone()
        }
    }

    impl FileSystem for MockFileSystem {
        fn create_dir_all(&self, path: &Path) -> Result<(), String> {
            self.created_dirs.borrow_mut().push(path.to_path_buf());
            self.dir_results.get(self.created_dirs.borrow().len() - 1)
                .cloned()
                .unwrap_or(Ok(()))
        }

        fn canonicalize(&self, path: &Path) -> Result<PathBuf, String> {
            self.canonicalized_paths.borrow_mut().push(path.to_path_buf());
            self.canonicalize_results.get(self.canonicalized_paths.borrow().len() - 1)
                .cloned()
                .unwrap_or(Ok(path.to_path_buf()))
        }
    }

    #[test]
    fn test_mock_filesystem() {
        let mock = MockFileSystem::new(
            vec![
                Ok(()),
                Err("mock dir error".to_string()),
                Ok(()),
            ],
            vec![
                Ok(PathBuf::from("/abs/test/dir1")),
                Err("mock canonicalize error".to_string()),
                Ok(PathBuf::from("/abs/test/dir3")),
            ],
        );

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

        assert!(mock.canonicalize(&path1).is_ok());
        assert!(mock.canonicalize(&path2).is_err());
        assert!(mock.canonicalize(&path3).is_ok());

        let canonicalized_paths = mock.get_canonicalized_paths();
        assert_eq!(canonicalized_paths.len(), 3);
        assert_eq!(canonicalized_paths[0], path1);
        assert_eq!(canonicalized_paths[1], path2);
        assert_eq!(canonicalized_paths[2], path3);
    }

} 