// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Provides utility functions for path processing
use crate::{
    error::{code, Error},
    vfs::{
        dcache::Dcache,
        file::{AccessMode, File, OpenFlags},
        inode_mode::{mode_t, InodeFileType, InodeMode},
        root::get_root_dir,
    },
};
use alloc::{string::String, sync::Arc};
use spin::{Mutex as SpinMutex, Once};

// FIXME: move WORKING_DIR to FsEnv
static WORKING_DIR: Once<SpinMutex<Arc<Dcache>>> = Once::new();

pub fn get_working_dir() -> Arc<Dcache> {
    WORKING_DIR
        .call_once(|| {
            let dir: &'static Arc<Dcache> = get_root_dir();
            SpinMutex::new(dir.clone())
        })
        .lock()
        .clone()
}

pub fn set_working_dir(dir: Arc<Dcache>) -> Result<(), Error> {
    let mut working_dir = WORKING_DIR.get().unwrap().lock();
    *working_dir = dir;
    Ok(())
}

enum FilePath<'a> {
    Absolute(&'a str),
    Relative(&'a str),
}

impl<'a> FilePath<'a> {
    pub fn new(path: &'a str) -> Self {
        if path.starts_with('/') {
            FilePath::Absolute(path)
        } else {
            FilePath::Relative(path)
        }
    }
}

pub fn lookup_path(path: &str) -> Option<Arc<Dcache>> {
    match FilePath::new(path) {
        FilePath::Absolute(path) => lookup_in_dir(get_root_dir(), path.trim_start_matches('/')),
        FilePath::Relative(path) => lookup_in_dir(&get_working_dir(), path),
    }
}

pub fn find_parent_and_name(path: &str) -> Option<(Arc<Dcache>, &str)> {
    match FilePath::new(path) {
        FilePath::Relative(path) => {
            let (parent, name) = split_path(path)?;
            let dir = get_working_dir();
            let parent = lookup_in_dir(&dir, parent)?;
            Some((parent, name))
        }
        FilePath::Absolute(path) => {
            let (parent, name) = split_path(path)?;
            let dir = get_root_dir();
            let parent = lookup_in_dir(dir, parent.trim_start_matches('/'))?;
            Some((parent, name))
        }
    }
}

pub fn open_path(path: &str, flags: i32, mode: mode_t) -> Result<File, Error> {
    // TODO: add support for symlink
    let open_flags = OpenFlags::from_bits_truncate(flags);
    let access_mode = AccessMode::from(flags);
    let dcache = match lookup_path(path) {
        Some(dcache) => {
            if open_flags.contains(OpenFlags::O_NOFOLLOW)
                && dcache.type_() == InodeFileType::SymLink
            {
                return Err(code::ELOOP);
            }
            if open_flags.contains(OpenFlags::O_CREAT) && open_flags.contains(OpenFlags::O_EXCL) {
                return Err(code::EEXIST);
            }
            if open_flags.contains(OpenFlags::O_DIRECTORY)
                && dcache.type_() != InodeFileType::Directory
            {
                return Err(code::ENOTDIR);
            }
            dcache
        }
        None => {
            if open_flags.contains(OpenFlags::O_CREAT) {
                if open_flags.contains(OpenFlags::O_DIRECTORY) || path.ends_with('/') {
                    return Err(code::ENOTDIR);
                }
                let Some((parent, name)) = find_parent_and_name(path) else {
                    return Err(code::ENOENT);
                };
                if !parent.mode().is_writable() {
                    return Err(code::EACCES);
                }

                parent.new_child(name, InodeFileType::Regular, InodeMode::from(mode), || None)?
            } else {
                return Err(code::ENOENT);
            }
        }
    };
    // resize to 0 if O_TRUNC is set
    if open_flags.contains(OpenFlags::O_TRUNC) && access_mode.is_writable() {
        dcache.inode().resize(0)?;
    }

    let file = File::new(dcache, AccessMode::from(flags), open_flags)?;
    Ok(file)
}

/// Split path into parent directory and filename
/// Returns (parent_path, file_name) or None
pub fn split_path(path: &str) -> Option<(&str, &str)> {
    if path.is_empty() {
        return None;
    }

    let (path_clean, end_with_slash) = match path.strip_suffix('/') {
        Some(p) => (p, true),
        None => (path, false),
    };

    if path_clean.is_empty() {
        return Some(("/", "."));
    }

    match path_clean.rsplit_once('/') {
        Some((parent, name)) => {
            let parent = if parent.is_empty() { "/" } else { parent };
            let name = if end_with_slash {
                &path[parent.len() + 1..]
            } else {
                name
            };
            Some((parent, name))
        }
        None => Some((".", path_clean)),
    }
}

/// Normalize path by removing "." and ".."
/// Returns normalized path or None
pub fn normalize_path(path: &str) -> Option<String> {
    if path.is_empty() {
        return None;
    }

    let is_absolute = path.starts_with('/');
    let mut result = String::with_capacity(path.len());
    let mut skip_count = 0;

    // Process path components in reverse order to handle ".." correctly
    for component in path.split('/').rev() {
        match component {
            "" | "." => continue,
            ".." => {
                skip_count += 1;
            }
            _ => {
                if skip_count > 0 {
                    skip_count -= 1;
                } else {
                    if !result.is_empty() {
                        result.insert(0, '/');
                    }
                    result.insert_str(0, component);
                }
            }
        }
    }

    // Handle remaining ".." for relative paths
    if !is_absolute {
        for _ in 0..skip_count {
            if !result.is_empty() {
                result.insert(0, '/');
            }
            result.insert_str(0, "..");
        }
    }

    // Handle empty result
    if result.is_empty() {
        result = if is_absolute {
            String::from("/")
        } else {
            String::from(".")
        };
    } else if is_absolute {
        result.insert(0, '/');
    }

    Some(result)
}

/// Join two paths
/// If path is absolute path then return path directly
pub fn join_path(base: &str, path: &str) -> Option<String> {
    if base.is_empty() {
        return normalize_path(path);
    }

    if path.starts_with('/') {
        return normalize_path(path);
    }

    let mut joined = String::from(base);
    if !base.ends_with('/') {
        joined.push('/');
    }
    joined.push_str(path);

    normalize_path(&joined)
}

/// Check if the path is valid
pub fn is_valid_path(path: &str) -> bool {
    if path.is_empty() {
        return false;
    }

    if path == "/" {
        return true;
    }

    let mut iter = path.split('/');

    // Handle absolute path
    if path.starts_with('/') {
        // First component should be empty for absolute path
        if !iter.next().unwrap_or("").is_empty() {
            return false;
        }
    }

    for component in iter {
        if component.is_empty() || component.contains('\0') {
            return false;
        }
    }

    true
}

fn lookup_in_dir(dir: &Arc<Dcache>, path: &str) -> Option<Arc<Dcache>> {
    // TODO: add support for symlink
    let mut current = dir.clone();
    let mut cur_path = path;

    while !cur_path.is_empty() {
        match cur_path.split_once('/') {
            Some((next_name, next_path)) => {
                let next_path = next_path.trim_start_matches('/');
                let next = current.lookup(next_name).ok()?;
                if next.type_() == InodeFileType::Directory {
                    current = next;
                    cur_path = next_path;
                } else {
                    // not a directory
                    return None;
                }
            }
            None => {
                // end of path, just find in cur dir
                current = current.lookup(cur_path).ok()?;
                break;
            }
        };
    }

    Some(current)
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::ToString;
    use blueos_test_macro::test;
    #[cfg(use_defmt)]
    use defmt::println;
    #[cfg(not(use_defmt))]
    use semihosting::println;

    #[test]
    fn test_is_valid_path() {
        // Valid paths
        assert!(is_valid_path("/"));
        assert!(is_valid_path("/usr"));
        assert!(is_valid_path("/usr/bin"));
        assert!(is_valid_path("usr/bin"));
        assert!(is_valid_path("./usr/bin"));
        assert!(is_valid_path("../usr/bin"));

        // Invalid paths
        assert!(!is_valid_path(""));
        assert!(!is_valid_path("//"));
        assert!(!is_valid_path("/usr//bin"));
        assert!(!is_valid_path("/usr/\0bin"));
        assert!(!is_valid_path("usr//bin"));
    }

    #[test]
    fn test_normalize_path() {
        // Absolute paths
        assert_eq!(normalize_path("/"), Some("/".to_string()));
        assert_eq!(normalize_path("/usr/bin"), Some("/usr/bin".to_string()));
        assert_eq!(normalize_path("/usr/./bin"), Some("/usr/bin".to_string()));
        assert_eq!(normalize_path("/usr/../bin"), Some("/bin".to_string()));
        assert_eq!(normalize_path("/usr/../../bin"), Some("/bin".to_string()));

        // Relative paths
        assert_eq!(normalize_path("usr/bin"), Some("usr/bin".to_string()));
        assert_eq!(normalize_path("./usr/bin"), Some("usr/bin".to_string()));
        assert_eq!(normalize_path("../usr/bin"), Some("../usr/bin".to_string()));
        assert_eq!(normalize_path("usr/./bin"), Some("usr/bin".to_string()));
        assert_eq!(normalize_path("usr/../bin"), Some("bin".to_string()));

        // Edge cases
        assert_eq!(normalize_path(""), None);
        assert_eq!(normalize_path("."), Some(".".to_string()));
        assert_eq!(normalize_path(".."), Some("..".to_string()));
    }

    #[test]
    fn test_split_path() {
        // Absolute paths
        assert_eq!(split_path("/usr/bin"), Some(("/usr", "bin")));
        assert_eq!(split_path("/usr/bin/"), Some(("/usr", "bin/")));
        assert_eq!(split_path("/usr/bin/test"), Some(("/usr/bin", "test")));
        assert_eq!(split_path("/usr"), Some(("/", "usr")));
        assert_eq!(split_path("/"), Some(("/", ".")));

        // Relative paths
        assert_eq!(split_path("usr/bin"), Some(("usr", "bin")));
        assert_eq!(split_path("usr/bin/"), Some(("usr", "bin/")));
        assert_eq!(split_path("usr/bin/test"), Some(("usr/bin", "test")));
        assert_eq!(split_path("bin"), Some((".", "bin")));

        // Edge cases
        assert_eq!(split_path(""), None);
    }

    #[test]
    fn test_join_path() {
        // Absolute paths
        assert_eq!(join_path("/usr", "/bin"), Some("/bin".to_string()));
        assert_eq!(join_path("/usr", "bin"), Some("/usr/bin".to_string()));
        assert_eq!(join_path("/usr/", "bin"), Some("/usr/bin".to_string()));

        // Relative paths
        assert_eq!(join_path("usr", "bin"), Some("usr/bin".to_string()));
        assert_eq!(join_path("usr/", "bin"), Some("usr/bin".to_string()));
        assert_eq!(join_path(".", "bin"), Some("bin".to_string()));
        assert_eq!(join_path("..", "bin"), Some("../bin".to_string()));

        // Edge cases
        assert_eq!(join_path("", "bin"), Some("bin".to_string()));
    }
}
