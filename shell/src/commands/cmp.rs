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

use std::fs::File;
use std::io::Read;

pub fn command(args: &[&str]) -> Result<(), String> {
    if args.len() != 2 {
        return Err("Usage: cmp <path1> <path2>".to_string());
    }

    let mut file1 =
        File::open(args[0]).map_err(|e| format!("Failed to open '{}': {}", args[0], e))?;
    let mut file2 =
        File::open(args[1]).map_err(|e| format!("Failed to open '{}': {}", args[1], e))?;

    let mut diff_bytes = 0;
    let mut total_size_diff = 0;

    let (mut buf1, mut buf2) = ([0u8; 512], [0u8; 512]);

    loop {
        let n1 = file1.read(&mut buf1).map_err(|e| e.to_string())?;
        let n2 = file2.read(&mut buf2).map_err(|e| e.to_string())?;

        if n1 == 0 && n2 == 0 {
            break;
        }

        if n1 != n2 {
            total_size_diff = if n1 > n2 {
                file1.read_to_end(&mut Vec::new()).unwrap_or_default() as i64 - n2 as i64
            } else {
                file2.read_to_end(&mut Vec::new()).unwrap_or_default() as i64 - n1 as i64
            };
            diff_bytes += (n1 as i64 - n2 as i64).unsigned_abs() as usize;
            break;
        }

        for i in 0..n1 {
            if buf1[i] != buf2[i] {
                diff_bytes += 1;
            }
        }
    }

    match (diff_bytes, total_size_diff) {
        (0, 0) => println!("Files are identical"),
        (_, 0) => println!("Found {} differing bytes", diff_bytes),
        (bytes, diff) => println!(
            "Files differ in length by {} bytes\nAdditionally found {} differing bytes",
            diff.abs(),
            bytes
        ),
    }

    Ok(())
}
