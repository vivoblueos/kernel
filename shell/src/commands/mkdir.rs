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

use std::{
    fs, io,
    os::unix::fs::PermissionsExt,
    path::{Path, PathBuf},
};

pub fn command(args: &[&str]) -> Result<(), String> {
    if args.is_empty() {
        return Err("Usage: mkdir [OPTION]... DIRECTORY...".to_string());
    }

    let mut parents = false;
    let mut verbose = false;
    let mut mode = None;
    let mut directories = Vec::new();

    let mut iter = args.iter();
    while let Some(arg) = iter.next() {
        match *arg {
            "-p" | "--parents" => parents = true,
            "-v" | "--verbose" => verbose = true,
            "-m" | "--mode" => {
                mode = iter.next().map(|s| parse_mode(s)).transpose()?.flatten();
            }
            _ if arg.starts_with('-') => return Err(format!("invalid option -- '{}'", arg)),
            _ => directories.push(arg),
        }
    }

    if directories.is_empty() {
        return Err("missing operand".to_string());
    }

    for dir in directories {
        let path = Path::new(dir);

        let result = if parents {
            create_dir_recursive(path)
        } else {
            fs::create_dir(path)
        };

        match result {
            Ok(_) => {
                if let Some(m) = mode {
                    if let Err(e) = set_permissions(path, m) {
                        return Err(format!("failed to set permissions for '{}': {}", dir, e));
                    }
                }
                if verbose {
                    println!("created directory '{}'", dir);
                }
            }
            Err(e) => {
                if parents && e.kind() == io::ErrorKind::AlreadyExists {
                    continue;
                }
                return Err(format!("cannot create directory '{}': {}", dir, e));
            }
        }
    }

    Ok(())
}

fn parse_mode(mode_str: &str) -> Result<Option<u32>, String> {
    if mode_str.is_empty() {
        return Ok(None);
    }

    u32::from_str_radix(mode_str, 8)
        .map_err(|_| format!("invalid mode '{}'", mode_str))
        .map(Some)
}

fn set_permissions(path: &Path, mode: u32) -> io::Result<()> {
    let permissions = fs::Permissions::from_mode(mode);
    fs::set_permissions(path, permissions)
}

fn create_dir_recursive(path: &Path) -> io::Result<()> {
    let mut current_path = PathBuf::new();
    for component in path.components() {
        current_path.push(component);
        if let Err(e) = fs::create_dir(&current_path) {
            if e.kind() != io::ErrorKind::AlreadyExists {
                return Err(e);
            }
        }
    }
    Ok(())
}
