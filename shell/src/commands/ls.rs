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

use std::{fs, os::unix::fs::MetadataExt, path::Path};

pub fn command(args: &[&str]) -> Result<(), String> {
    let mut show_hidden = false;
    let mut long_format = false;
    let mut target_path = ".";

    for arg in args {
        match arg {
            &"-a" => show_hidden = true,
            &"-l" => long_format = true,
            &"-la" | &"-al" => {
                show_hidden = true;
                long_format = true;
            }
            path if !path.starts_with('-') => target_path = path,
            _ => return Err(format!("Unknown option: {}", arg)),
        }
    }

    let path = Path::new(target_path);

    if !path.exists() {
        return Err(format!("Directory does not exist: {}", target_path));
    }

    let entries = fs::read_dir(path).map_err(|e| format!("Unable to read directory: {}", e))?;
    let mut items: Vec<_> = entries
        .filter_map(|entry| entry.ok())
        .filter(|entry| entry.path().file_name().is_some())
        .collect();
    items.sort_by(|a, b| {
        a.path()
            .file_name()
            .unwrap_or_default()
            .cmp(b.path().file_name().unwrap_or_default())
    });

    for entry in items {
        let path = entry.path();
        let file_name = path.file_name().unwrap_or_default().to_string_lossy();

        if !show_hidden && file_name.starts_with('.') {
            continue;
        }

        if long_format {
            let metadata = entry
                .metadata()
                .map_err(|e| format!("Unable to obtain file information: {}", e))?;
            let file_type = if path.is_dir() { "d" } else { "-" };
            let perms = metadata.mode();

            let mode = format!(
                "{}{}{}{}{}{}{}{}{}",
                if perms & 0o400 != 0 { "r" } else { "-" },
                if perms & 0o200 != 0 { "w" } else { "-" },
                if perms & 0o100 != 0 { "x" } else { "-" },
                if perms & 0o40 != 0 { "r" } else { "-" },
                if perms & 0o20 != 0 { "w" } else { "-" },
                if perms & 0o10 != 0 { "x" } else { "-" },
                if perms & 0o4 != 0 { "r" } else { "-" },
                if perms & 0o2 != 0 { "w" } else { "-" },
                if perms & 0o1 != 0 { "x" } else { "-" },
            );

            let size = format_size(metadata.len());
            println!("{}{} {} {}", file_type, mode, size, file_name);
        } else if path.is_dir() {
            println!("{}/", file_name);
        } else {
            println!("{}", file_name);
        }
    }

    Ok(())
}

fn format_size(size: u64) -> String {
    const KB: u64 = 1024;
    const MB: u64 = KB * 1024;
    const GB: u64 = MB * 1024;

    if size < KB {
        format!("{}B", size)
    } else if size < MB {
        format!("{:.1}K", size as f64 / KB as f64)
    } else if size < GB {
        format!("{:.1}M", size as f64 / MB as f64)
    } else {
        format!("{:.1}G", size as f64 / GB as f64)
    }
}
