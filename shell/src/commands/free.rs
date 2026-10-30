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

use std::{fs, path::Path};

pub fn command(_args: &[&str]) -> Result<(), String> {
    println!("{:<12} {:<12} {:<12}", "total", "used", "free");
    let meminfo = Path::new("/proc/meminfo");
    let content =
        fs::read_to_string(meminfo).map_err(|e| format!("Failed to read /proc/meminfo: {}", e))?;
    let mut total = "0".to_string();
    let mut used = "0".to_string();
    let mut free = "0".to_string();
    for line in content.lines() {
        if let Some((key, value)) = line.split_once(':') {
            match key.trim() {
                "MemTotal" => total = value.split_whitespace().next().unwrap_or("").to_string(),
                "MemUsed" => used = value.split_whitespace().next().unwrap_or("").to_string(),
                "MemAvailable" => free = value.split_whitespace().next().unwrap_or("").to_string(),
                _ => {}
            }
        }
    }

    println!("{:<12} {:<12} {:<12}", total, used, free);

    Ok(())
}
