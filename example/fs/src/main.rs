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

extern crate librs;
extern crate rsrt;
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::Path;

fn main() -> std::io::Result<()> {
    println!("=== BlueOS File System Example ===");

    run_tmpfs()?;

    run_fatfs()?;

    println!("\n=== File System Example Completed Successfully ===");
    Ok(())
}

fn run_tmpfs() -> std::io::Result<()> {
    let directories = [
        "/tmp",
        "/tmp/test_dir",
        "/tmp/test_dir/subdir1",
        "/tmp/test_dir/subdir2",
        "/tmp/test_dir/subdir1/nested",
    ];

    // Step 1: Create directory structure
    println!("\n1. Creating directory structure...");
    create_directory_structure(&directories)?;

    // Step 2: Create and write to files
    println!("\n2. Creating and writing to files...");
    create_and_write_files("/tmp")?;

    // Step 3: Read from files
    println!("\n3. Reading from files...");
    read_files("/tmp")?;

    // Step 4: List directory contents
    println!("\n4. Listing directory contents...");
    list_directory_contents("/tmp")?;

    // Step 5: File operations (copy, move, delete)
    println!("\n5. Performing file operations...");
    perform_file_operations("/tmp")?;

    Ok(())
}

fn run_fatfs() -> std::io::Result<()> {
    let is_exist = Path::new("/fat").exists();
    if !is_exist {
        println!("Fatfs is not mounted");
        return Ok(());
    }

    let directories = [
        "/fat",
        "/fat/test_dir",
        "/fat/test_dir/subdir1",
        "/fat/test_dir/subdir2",
        "/fat/test_dir/subdir1/nested",
    ];

    // Step 1: Create directory structure
    println!("\n1. Creating directory structure...");
    create_directory_structure(&directories)?;

    // Step 2: Create and write to files
    println!("\n2. Creating and writing to files...");
    create_and_write_files("/fat")?;

    // Step 3: Read from files
    println!("\n3. Reading from files...");
    read_files("/fat")?;

    // Step 4: List directory contents
    println!("\n4. Listing directory contents...");
    list_directory_contents("/fat")?;

    // Step 5: File operations (copy, move, delete)
    println!("\n5. Performing file operations...");
    perform_file_operations("/fat")?;

    Ok(())
}

/// Create a sample directory structure
fn create_directory_structure(directories: &[&str]) -> std::io::Result<()> {
    for dir in directories {
        fs::create_dir_all(dir)?;
        println!("Created directory: {}", dir);
    }

    Ok(())
}

/// Create files and write content to them
fn create_and_write_files(root: &str) -> std::io::Result<()> {
    // Create a text file
    let text_content = "Hello, BlueOS!\nThis is a sample text file.\nRust file system operations are working great!";
    fs::write(format!("{}/test_dir/hello.txt", root), text_content)?;
    println!("Created and wrote to: {}/test_dir/hello.txt", root);

    // Create a configuration file
    let config_content = r#"# Sample configuration file
[app]
name = "BlueOS Example"
version = "1.0.0"
debug = true

[filesystem]
tmp_dir = "/tmp"
max_size = "100MB"
"#;
    fs::write(format!("{}/test_dir/config.toml", root), config_content)?;
    println!("Created and wrote to: {}/test_dir/config.toml", root);

    // Create a binary file with some data
    let binary_data = vec![
        0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x20, 0x42, 0x6c, 0x75, 0x65, 0x4f, 0x53,
    ]; // "Hello BlueOS"
    fs::write(format!("{}/test_dir/data.bin", root), binary_data)?;
    println!("Created and wrote to: {}/test_dir/data.bin", root);

    // Create a file in subdirectory
    let subdir_content =
        "This file is in a subdirectory.\nIt demonstrates nested directory operations.";
    fs::write(
        format!("{}/test_dir/subdir1/nested/file.txt", root),
        subdir_content,
    )?;
    println!(
        "Created and wrote to: {}/test_dir/subdir1/nested/file.txt",
        root
    );

    // Append to an existing file
    let mut file = OpenOptions::new()
        .write(true)
        .append(true)
        .create(true)
        .open(format!("{}/test_dir/log.txt", root))?;

    writeln!(file, "[2024-01-01 12:00:00] Application started")?;
    writeln!(
        file,
        "[2024-01-01 12:00:01] File system operations completed"
    )?;
    println!("Created and appended to: {}/test_dir/log.txt", root);

    Ok(())
}

/// Read content from various files
fn read_files(root: &str) -> std::io::Result<()> {
    // Read text file
    let text_content = fs::read_to_string(format!("{}/test_dir/hello.txt", root))?;
    println!("Content of hello.txt:\n{}", text_content);

    // Read configuration file
    let config_content = fs::read_to_string(format!("{}/test_dir/config.toml", root))?;
    println!("Content of config.toml:\n{}", config_content);

    // Read binary file
    let binary_data = fs::read(format!("{}/test_dir/data.bin", root))?;
    println!("Binary data (hex): {:02x?}", binary_data);

    // Read file in subdirectory
    let subdir_content = fs::read_to_string(format!("{}/test_dir/subdir1/nested/file.txt", root))?;
    println!("Content of nested file.txt:\n{}", subdir_content);

    // Read log file
    let log_content = fs::read_to_string(format!("{}/test_dir/log.txt", root))?;
    println!("Content of log.txt:\n{}", log_content);

    Ok(())
}

/// List contents of directories
fn list_directory_contents(root: &str) -> std::io::Result<()> {
    let path = format!("{}/test_dir", root);
    println!("Contents of {}:", path);
    list_directory(&path)?;

    let path = format!("{}/test_dir/subdir1", root);
    println!("\nContents of {}:", path);
    list_directory(&path)?;

    let path = format!("{}/test_dir/subdir1/nested", root);
    println!("\nContents of {}:", path);
    list_directory(&path)?;

    Ok(())
}

/// Helper function to list directory contents
fn list_directory(path: &str) -> std::io::Result<()> {
    let entries = fs::read_dir(path)?;

    for entry in entries {
        let entry = entry?;
        let path = entry.path();
        let metadata = entry.metadata()?;

        if metadata.is_file() {
            let size = metadata.len();
            println!(
                "  📄 {} ({} bytes)",
                path.file_name().unwrap().to_string_lossy(),
                size
            );
        } else if metadata.is_dir() {
            println!("  📁 {}", path.file_name().unwrap().to_string_lossy());
        }
    }

    Ok(())
}

/// Perform various file operations
fn perform_file_operations(root: &str) -> std::io::Result<()> {
    // Copy a file
    fs::copy(
        format!("{}/test_dir/hello.txt", root),
        format!("{}/test_dir/hello_copy.txt", root),
    )?;
    println!("Copied hello.txt to hello_copy.txt");

    // Move/rename a file
    fs::rename(
        format!("{}/test_dir/config.toml", root),
        format!("{}/test_dir/app_config.toml", root),
    )?;
    println!("Renamed config.toml to app_config.toml");

    // Get file metadata
    let metadata = fs::metadata(format!("{}/test_dir/hello.txt", root))?;
    println!("File metadata for hello.txt:");
    println!("  Size: {} bytes", metadata.len());
    println!("  Permissions: {:?}", metadata.permissions());
    println!("  Modified: {:?}", metadata.modified()?);

    // Check if files exist
    println!("File existence check:");
    println!(
        "  hello.txt exists: {}",
        Path::new(format!("{}/test_dir/hello.txt", root).as_str()).exists()
    );
    println!(
        "  nonexistent.txt exists: {}",
        Path::new(format!("{}/test_dir/nonexistent.txt", root).as_str()).exists()
    );

    // Delete a file
    fs::remove_file(format!("{}/test_dir/hello_copy.txt", root))?;
    println!("Deleted hello_copy.txt");

    Ok(())
}
