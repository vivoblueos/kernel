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
    io::{Read, Write},
    path::Path,
};

pub fn command(args: &[&str]) -> Result<(), String> {
    if args.len() != 2 {
        return Err("Usage: cp <source file> <destination file/dir>".to_string());
    }

    let src = Path::new(args[0]);
    let dst = Path::new(args[1]);

    if !src.exists() {
        return Err(format!("Source file '{}' does not exist", src.display()));
    }

    if src.is_dir() {
        return Err("Copying directories is not supported".to_string());
    }

    let dst_path = if dst.is_dir() {
        // If destination is a directory, append the source file name.
        dst.join(src.file_name().ok_or("Invalid source filename")?)
    } else {
        // If destination is a file, use it directly.
        dst.to_path_buf()
    };

    copy_file_using_read_write(src, &dst_path)?;

    Ok(())
}

fn copy_file_using_read_write(src: &Path, dst: &Path) -> Result<(), String> {
    let mut src_file = File::open(src)
        .map_err(|e| format!("Failed to open source file '{}': {}", src.display(), e))?;

    let mut dst_file = File::create(dst).map_err(|e| {
        format!(
            "Failed to create destination file '{}': {}",
            dst.display(),
            e
        )
    })?;

    let mut buffer = vec![0; 512];

    loop {
        let bytes_read = src_file
            .read(&mut buffer)
            .map_err(|e| format!("Failed to read from '{}': {}", src.display(), e))?;

        if bytes_read == 0 {
            break;
        }

        dst_file
            .write_all(&buffer[..bytes_read])
            .map_err(|e| format!("Failed to write to '{}': {}", dst.display(), e))?;
    }

    dst_file
        .flush()
        .map_err(|e| format!("Failed to flush '{}': {}", dst.display(), e))?;

    Ok(())
}
