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

extern crate ftp;
extern crate librs;
extern crate rsrt;

use ftp::{FtpError, FtpStream};
use std::{io::Cursor, str};

// ftp server configuration
const FTP_ADDR: &str = "127.0.0.1";
const FTP_PORT: u16 = 21;
const FTP_USERNAME: &str = "testftp";
const FTP_PASSWORD: &str = "12345678";

fn main() -> std::io::Result<()> {
    println!("\n=== FTP Client Example Start ===");

    if let Err(e) = read_file_from_server() {
        eprintln!("Failed to read file from server: {e:?}\n");
    } else {
        println!("Read file from server success.\n");
    }

    if let Err(e) = upload_file_to_server() {
        eprintln!("Failed to upload file to server: {e:?}\n");
    } else {
        println!("Upload file to server success.\n");
    }

    println!("=== FTP Client Example End ===\n");
    Ok(())
}

/// Reads `hello_ftp_client.txt` from the FTP server root directory
fn read_file_from_server() -> Result<(), FtpError> {
    // Connect & login
    let mut ftp_stream = FtpStream::connect((FTP_ADDR, FTP_PORT))?;
    ftp_stream.login(FTP_USERNAME, FTP_PASSWORD)?;
    println!("Current dir: {}", ftp_stream.pwd()?);

    // Download file
    let bytes = ftp_stream.simple_retr("hello_ftp_client.txt")?.into_inner();
    let contents = str::from_utf8(&bytes).map_err(|e| {
        eprintln!("UTF-8 decode error: {e:?}");
        FtpError::InvalidResponse("Invalid UTF-8 data".into())
    })?;
    println!("Contents of hello_ftp_client.txt:\n{contents}");

    ftp_stream.quit()?;
    Ok(())
}

/// Uploads `file_from_ftp_client.txt` to `/blueos_upload_data` directory on the FTP server
fn upload_file_to_server() -> Result<(), FtpError> {
    // Connect & login
    let mut ftp_stream = FtpStream::connect((FTP_ADDR, FTP_PORT))?;
    ftp_stream.login(FTP_USERNAME, FTP_PASSWORD)?;
    println!("Current dir: {}", ftp_stream.pwd()?);

    // Change to target upload directory
    ftp_stream.cwd("blueos_upload_data")?;

    let content = r#"Hello, Server!
        This is a message from blueos FTP client:
        李白乘舟将欲行，
        忽闻岸上踏歌声。
        桃花潭水深千尺，
        不及汪伦送我情。
        End of message!"#;
    let mut reader = Cursor::new(content.as_bytes());

    // Upload file
    ftp_stream.put("file_from_ftp_client.txt", &mut reader)?;

    ftp_stream.quit()?;
    Ok(())
}
