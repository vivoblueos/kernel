use std::env;
use std::fs::File;
use std::io;

use chrono::NaiveDateTime;
use fatfs::{FileSystem, FsOptions};
use fscommon::BufStream;

fn format_file_size(size: u64) -> String {
    const KB: u64 = 1024;
    const MB: u64 = 1024 * KB;
    const GB: u64 = 1024 * MB;
    if size < KB {
        format!("{}B", size)
    } else if size < MB {
        format!("{}KB", size / KB)
    } else if size < GB {
        format!("{}MB", size / MB)
    } else {
        format!("{}GB", size / GB)
    }
}

fn main() -> io::Result<()> {
    let file = File::open("resources/fat32.img")?;
    let buf_rdr = BufStream::new(file);
    let fs = FileSystem::new(buf_rdr, FsOptions::new())?;
    let root_dir = fs.root_dir();
    let dir = match env::args().nth(1) {
        None => root_dir,
        Some(ref path) if path == "." => root_dir,
        Some(ref path) => root_dir.open_dir(path)?,
    };
    for r in dir.iter() {
        let e = r?;
        let modified = NaiveDateTime::from(e.modified())
            .format("%Y-%m-%d %H:%M:%S")
            .to_string();
        println!("{:4}  {}  {}", format_file_size(e.len()), modified, e.file_name());
    }
    Ok(())
}
