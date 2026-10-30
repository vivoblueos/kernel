use std::fs::OpenOptions;
use std::io::{self, prelude::*};

use fatfs::{FileSystem, FsOptions};
use fscommon::BufStream;

fn main() -> io::Result<()> {
    let img_file = match OpenOptions::new().read(true).write(true).open("fat.img") {
        Ok(file) => file,
        Err(err) => {
            println!("Failed to open image!");
            return Err(err);
        }
    };
    let buf_stream = BufStream::new(img_file);
    let options = FsOptions::new().update_accessed_date(true);
    let fs = FileSystem::new(buf_stream, options)?;
    let mut file = fs.root_dir().create_file("hello.txt")?;
    file.write_all(b"Hello World!")?;
    Ok(())
}
