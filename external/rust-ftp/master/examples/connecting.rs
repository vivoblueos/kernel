extern crate ftp;
#[cfg(target_os = "blueos")]
extern crate librs;
#[cfg(target_os = "blueos")]
extern crate rsrt;

use ftp::{FtpError, FtpStream};
use std::{io::Cursor, str};

fn test_ftp(addr: &str, user: &str, pass: &str) -> Result<(), FtpError> {
    let mut ftp_stream = FtpStream::connect((addr, 21)).unwrap();

    ftp_stream.login(user, pass).unwrap();
    println!("current dir: {}", ftp_stream.pwd().unwrap());

    ftp_stream.cwd("test_data").unwrap();

    // An easy way to retrieve a file
    let cursor = ftp_stream.simple_retr("ftpext-charter.txt").unwrap();
    let vec = cursor.into_inner();
    let text = str::from_utf8(&vec).unwrap();
    println!("got data: {}", text);

    // Store a file
    #[allow(clippy::useless_format)]
    let file_data = format!("Some awesome file data man!!");
    let mut reader = Cursor::new(file_data.into_bytes());
    ftp_stream.put("my_random_file.txt", &mut reader).unwrap();

    ftp_stream.quit()
}

fn main() {
    test_ftp("127.0.0.1", "anonymous", "rust-ftp@github.com").unwrap();
    println!("test successful")
}
