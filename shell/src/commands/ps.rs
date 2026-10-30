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

use std::{fs, io, path::Path};

pub fn command(_args: &[&str]) -> Result<(), String> {
    println!("{:<10} {:<10} {:<9} KIND", "TID", "STATUS", "PRIORITY");
    let proc_dir = Path::new("/proc");

    for entry in fs::read_dir(proc_dir).map_err(|e| format!("Failed to read /proc: {}", e))? {
        let entry = entry.map_err(|e| format!("Failed to read dir entry: {}", e))?;
        let file_name = entry.file_name();
        let pid_str = file_name.to_string_lossy();
        if let Ok(pid) = pid_str.parse::<u32>() {
            let status = read_process_status(&entry.path()).unwrap_or_default();
            // cmdline is not supported yet
            // let cmdline = read_process_cmdline(&entry.path()).unwrap_or_default();

            println!(
                "{:<10} {:<10} {:<9} {}",
                pid,
                status.state.unwrap(),
                status.priority.unwrap(),
                status.name.unwrap(),
            );
        }
    }
    Ok(())
}

fn read_process_status(proc_path: &Path) -> io::Result<ProcessStatus> {
    let status_path = proc_path.join("status");
    let content = fs::read_to_string(status_path)?;

    let mut status = ProcessStatus::default();

    for line in content.lines() {
        if let Some((key, value)) = line.split_once(':') {
            match key.trim() {
                "Name" => status.name = Some(value.trim().to_string()),
                "State" => {
                    status.state = Some(value.split_whitespace().next().unwrap_or("").to_string())
                }
                "Priority" => status.priority = Some(value.trim().to_string()),
                _ => {}
            }
        }
    }

    Ok(status)
}

fn read_process_cmdline(proc_path: &Path) -> io::Result<Vec<String>> {
    let cmdline_path = proc_path.join("cmdline");
    let content = fs::read_to_string(cmdline_path)?;

    Ok(content
        .split('\0')
        .filter(|s| !s.is_empty())
        .map(|s| s.to_string())
        .collect())
}

#[derive(Default)]
struct ProcessStatus {
    name: Option<String>,
    state: Option<String>,
    priority: Option<String>,
}
