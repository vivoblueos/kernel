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

use std::fs::OpenOptions;

pub fn command(args: &[&str]) -> Result<(), String> {
    if args.len() != 2 {
        return Err("Usage: truncate <file> <size>".to_string());
    }

    let filename = args[0];
    let size: u64 = args[1]
        .parse()
        .map_err(|_| "Invalid size value".to_string())?;

    let file = OpenOptions::new()
        .read(true)
        .write(true)
        .open(filename)
        .map_err(|e| format!("Unable to open file '{}': {}", filename, e))?;

    file.set_len(size)
        .map_err(|e| format!("Unable to set file size: {}", e))?;

    Ok(())
}
