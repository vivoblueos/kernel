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
    fs::File,
    io::{BufRead, BufReader},
};

pub fn command(args: &[&str]) -> Result<(), String> {
    if args.is_empty() {
        return Err("Usage: cat [<path> [<path> [<path> ...]]]".to_string());
    }
    for filename in args {
        let file = File::open(filename)
            .map_err(|e| format!("unable to open file '{}': {}", filename, e))?;
        let reader = BufReader::new(file);
        for line in reader.lines() {
            println!(
                "{}",
                line.map_err(|e| format!("reading file failed: {}", e))?
            );
        }
    }
    Ok(())
}
