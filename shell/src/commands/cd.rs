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

use std::{env, path::Path};

pub fn command(args: &[&str]) -> Result<(), String> {
    if args.len() != 1 {
        return Err("Usage: cd <directory>".to_string());
    }
    let target = args[0];
    let target_path = match target {
        "." => env::current_dir().map_err(|e| format!("Unable to get current directory: {}", e))?,
        path => {
            let current_dir = env::current_dir()
                .map_err(|e| format!("Unable to get current directory: {}", e))?;
            let mut path_buf = current_dir;
            for component in Path::new(path).components() {
                match component {
                    std::path::Component::ParentDir => {
                        if !path_buf.pop() {
                            return Err("Already at root directory".to_string());
                        }
                    }
                    std::path::Component::Normal(dir) => {
                        path_buf.push(dir);
                    }
                    _ => {}
                }
            }
            path_buf
        }
    };
    if let Err(e) = env::set_current_dir(&target_path) {
        Err(format!(
            "Unable to change directory to '{}': {}",
            target_path.display(),
            e
        ))
    } else {
        Ok(())
    }
}
