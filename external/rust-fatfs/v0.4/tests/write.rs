use std::fs;
use std::io;
use std::io::prelude::*;
use std::mem;
use std::str;

use fatfs::{FsOptions, StdIoWrapper};
use fscommon::BufStream;

const FAT12_IMG: &str = "fat12.img";
const FAT16_IMG: &str = "fat16.img";
const FAT32_IMG: &str = "fat32.img";
const IMG_DIR: &str = "resources";
const TMP_DIR: &str = "tmp";
const TEST_STR: &str = "Hi there Rust programmer!\n";
const TEST_STR2: &str = "Rust is cool!\n";

type FileSystem = fatfs::FileSystem<StdIoWrapper<BufStream<fs::File>>>;

fn call_with_tmp_img<F: Fn(&str)>(f: F, filename: &str, test_seq: u32) {
    let _ = env_logger::builder().is_test(true).try_init();
    let img_path = format!("{}/{}", IMG_DIR, filename);
    let tmp_path = format!("{}/{}-{}", TMP_DIR, test_seq, filename);
    fs::create_dir(TMP_DIR).ok();
    fs::copy(img_path, &tmp_path).unwrap();
    f(tmp_path.as_str());
    fs::remove_file(tmp_path).unwrap();
}

fn open_filesystem_rw(tmp_path: &str) -> FileSystem {
    let file = fs::OpenOptions::new().read(true).write(true).open(tmp_path).unwrap();
    let buf_file = BufStream::new(file);
    let options = FsOptions::new().update_accessed_date(true);
    FileSystem::new(buf_file, options).unwrap()
}

fn call_with_fs<F: Fn(FileSystem)>(f: F, filename: &str, test_seq: u32) {
    let callback = |tmp_path: &str| {
        let fs = open_filesystem_rw(tmp_path);
        f(fs);
    };
    call_with_tmp_img(callback, filename, test_seq);
}

fn test_write_short_file(fs: FileSystem) {
    let root_dir = fs.root_dir();
    let mut file = root_dir.open_file("short.txt").expect("open file");
    file.truncate().unwrap();
    file.write_all(TEST_STR.as_bytes()).unwrap();
    file.seek(io::SeekFrom::Start(0)).unwrap();
    let mut buf = Vec::new();
    file.read_to_end(&mut buf).unwrap();
    assert_eq!(TEST_STR, str::from_utf8(&buf).unwrap());
}

#[test]
fn test_write_file_fat12() {
    call_with_fs(test_write_short_file, FAT12_IMG, 1)
}

#[test]
fn test_write_file_fat16() {
    call_with_fs(test_write_short_file, FAT16_IMG, 1)
}

#[test]
fn test_write_file_fat32() {
    call_with_fs(test_write_short_file, FAT32_IMG, 1)
}

fn test_write_long_file(fs: FileSystem) {
    let root_dir = fs.root_dir();
    let mut file = root_dir.open_file("long.txt").expect("open file");
    file.truncate().unwrap();
    let test_str = TEST_STR.repeat(1000);
    file.write_all(test_str.as_bytes()).unwrap();
    file.seek(io::SeekFrom::Start(0)).unwrap();
    let mut buf = Vec::new();
    file.read_to_end(&mut buf).unwrap();
    assert_eq!(test_str, str::from_utf8(&buf).unwrap());
    file.seek(io::SeekFrom::Start(1234)).unwrap();
    file.truncate().unwrap();
    file.seek(io::SeekFrom::Start(0)).unwrap();
    buf.clear();
    file.read_to_end(&mut buf).unwrap();
    assert_eq!(&test_str[..1234], str::from_utf8(&buf).unwrap());
}

#[test]
fn test_write_long_file_fat12() {
    call_with_fs(test_write_long_file, FAT12_IMG, 2)
}

#[test]
fn test_write_long_file_fat16() {
    call_with_fs(test_write_long_file, FAT16_IMG, 2)
}

#[test]
fn test_write_long_file_fat32() {
    call_with_fs(test_write_long_file, FAT32_IMG, 2)
}

fn test_remove(fs: FileSystem) {
    let root_dir = fs.root_dir();
    assert!(root_dir.remove("very/long/path").is_err());
    let dir = root_dir.open_dir("very/long/path").unwrap();
    let mut names = dir.iter().map(|r| r.unwrap().file_name()).collect::<Vec<String>>();
    assert_eq!(names, [".", "..", "test.txt"]);
    root_dir.remove("very/long/path/test.txt").unwrap();
    names = dir.iter().map(|r| r.unwrap().file_name()).collect::<Vec<String>>();
    assert_eq!(names, [".", ".."]);
    assert!(root_dir.remove("very/long/path").is_ok());

    names = root_dir.iter().map(|r| r.unwrap().file_name()).collect::<Vec<String>>();
    assert_eq!(names, ["long.txt", "short.txt", "very", "very-long-dir-name"]);
    root_dir.remove("long.txt").unwrap();
    names = root_dir.iter().map(|r| r.unwrap().file_name()).collect::<Vec<String>>();
    assert_eq!(names, ["short.txt", "very", "very-long-dir-name"]);
}

#[test]
fn test_remove_fat12() {
    call_with_fs(test_remove, FAT12_IMG, 3)
}

#[test]
fn test_remove_fat16() {
    call_with_fs(test_remove, FAT16_IMG, 3)
}

#[test]
fn test_remove_fat32() {
    call_with_fs(test_remove, FAT32_IMG, 3)
}

fn test_create_file(fs: FileSystem) {
    let root_dir = fs.root_dir();
    let dir = root_dir.open_dir("very/long/path").unwrap();
    let mut names = dir.iter().map(|r| r.unwrap().file_name()).collect::<Vec<String>>();
    assert_eq!(names, [".", "..", "test.txt"]);
    {
        // test some invalid names
        assert!(root_dir.create_file("very/long/path/:").is_err());
        assert!(root_dir.create_file("very/long/path/\0").is_err());
        // create file
        let mut file = root_dir
            .create_file("very/long/path/new-file-with-long-name.txt")
            .unwrap();
        file.write_all(TEST_STR.as_bytes()).unwrap();
    }
    // check for dir entry
    names = dir.iter().map(|r| r.unwrap().file_name()).collect::<Vec<String>>();
    assert_eq!(names, [".", "..", "test.txt", "new-file-with-long-name.txt"]);
    names = dir
        .iter()
        .map(|r| r.unwrap().short_file_name())
        .collect::<Vec<String>>();
    assert_eq!(names, [".", "..", "TEST.TXT", "NEW-FI~1.TXT"]);
    {
        // check contents
        let mut file = root_dir
            .open_file("very/long/path/new-file-with-long-name.txt")
            .unwrap();
        let mut content = String::new();
        file.read_to_string(&mut content).unwrap();
        assert_eq!(&content, &TEST_STR);
    }
    // Create enough entries to allocate next cluster
    for i in 0..512 / 32 {
        let name = format!("test{}", i);
        dir.create_file(&name).unwrap();
    }
    names = dir.iter().map(|r| r.unwrap().file_name()).collect::<Vec<String>>();
    assert_eq!(names.len(), 4 + 512 / 32);
    // check creating existing file opens it
    {
        let mut file = root_dir
            .create_file("very/long/path/new-file-with-long-name.txt")
            .unwrap();
        let mut content = String::new();
        file.read_to_string(&mut content).unwrap();
        assert_eq!(&content, &TEST_STR);
    }
    // check using create_file with existing directory fails
    assert!(root_dir.create_file("very").is_err());
}

#[test]
fn test_create_file_fat12() {
    call_with_fs(test_create_file, FAT12_IMG, 4)
}

#[test]
fn test_create_file_fat16() {
    call_with_fs(test_create_file, FAT16_IMG, 4)
}

#[test]
fn test_create_file_fat32() {
    call_with_fs(test_create_file, FAT32_IMG, 4)
}

fn test_create_dir(fs: FileSystem) {
    let root_dir = fs.root_dir();
    let parent_dir = root_dir.open_dir("very/long/path").unwrap();
    let mut names = parent_dir
        .iter()
        .map(|r| r.unwrap().file_name())
        .collect::<Vec<String>>();
    assert_eq!(names, [".", "..", "test.txt"]);
    {
        let subdir = root_dir.create_dir("very/long/path/new-dir-with-long-name").unwrap();
        names = subdir.iter().map(|r| r.unwrap().file_name()).collect::<Vec<String>>();
        assert_eq!(names, [".", ".."]);
    }
    // check if new entry is visible in parent
    names = parent_dir
        .iter()
        .map(|r| r.unwrap().file_name())
        .collect::<Vec<String>>();
    assert_eq!(names, [".", "..", "test.txt", "new-dir-with-long-name"]);
    {
        // Check if new directory can be opened and read
        let subdir = root_dir.open_dir("very/long/path/new-dir-with-long-name").unwrap();
        names = subdir.iter().map(|r| r.unwrap().file_name()).collect::<Vec<String>>();
        assert_eq!(names, [".", ".."]);
    }
    // Check if '.' is alias for new directory
    {
        let subdir = root_dir.open_dir("very/long/path/new-dir-with-long-name/.").unwrap();
        names = subdir.iter().map(|r| r.unwrap().file_name()).collect::<Vec<String>>();
        assert_eq!(names, [".", ".."]);
    }
    // Check if '..' is alias for parent directory
    {
        let subdir = root_dir.open_dir("very/long/path/new-dir-with-long-name/..").unwrap();
        names = subdir.iter().map(|r| r.unwrap().file_name()).collect::<Vec<String>>();
        assert_eq!(names, [".", "..", "test.txt", "new-dir-with-long-name"]);
    }
    // check if creating existing directory returns it
    {
        let subdir = root_dir.create_dir("very").unwrap();
        names = subdir.iter().map(|r| r.unwrap().file_name()).collect::<Vec<String>>();
        assert_eq!(names, [".", "..", "long"]);
    }
    // check short names validity after create_dir
    {
        let subdir = root_dir.create_dir("test").unwrap();
        names = subdir
            .iter()
            .map(|r| r.unwrap().short_file_name())
            .collect::<Vec<String>>();
        assert_eq!(names, [".", ".."]);
    }

    // check using create_dir with existing file fails
    assert!(root_dir.create_dir("very/long/path/test.txt").is_err());
}

#[test]
fn test_create_dir_fat12() {
    call_with_fs(test_create_dir, FAT12_IMG, 5)
}

#[test]
fn test_create_dir_fat16() {
    call_with_fs(test_create_dir, FAT16_IMG, 5)
}

#[test]
fn test_create_dir_fat32() {
    call_with_fs(test_create_dir, FAT32_IMG, 5)
}

fn test_rename_file(fs: FileSystem) {
    let root_dir = fs.root_dir();
    let parent_dir = root_dir.open_dir("very/long/path").unwrap();
    let entries = parent_dir.iter().map(|r| r.unwrap()).collect::<Vec<_>>();
    let names = entries.iter().map(|r| r.file_name()).collect::<Vec<_>>();
    assert_eq!(names, [".", "..", "test.txt"]);
    assert_eq!(entries[2].len(), 14);
    let stats = fs.stats().unwrap();

    parent_dir.rename("test.txt", &parent_dir, "new-long-name.txt").unwrap();
    let entries = parent_dir.iter().map(|r| r.unwrap()).collect::<Vec<_>>();
    let names = entries.iter().map(|r| r.file_name()).collect::<Vec<_>>();
    assert_eq!(names, [".", "..", "new-long-name.txt"]);
    assert_eq!(entries[2].len(), TEST_STR2.len() as u64);
    let mut file = parent_dir.open_file("new-long-name.txt").unwrap();
    let mut buf = Vec::new();
    file.read_to_end(&mut buf).unwrap();
    assert_eq!(str::from_utf8(&buf).unwrap(), TEST_STR2);

    parent_dir
        .rename("new-long-name.txt", &root_dir, "moved-file.txt")
        .unwrap();
    let entries = root_dir.iter().map(|r| r.unwrap()).collect::<Vec<_>>();
    let names = entries.iter().map(|r| r.file_name()).collect::<Vec<_>>();
    assert_eq!(
        names,
        ["long.txt", "short.txt", "very", "very-long-dir-name", "moved-file.txt"]
    );
    assert_eq!(entries[4].len(), TEST_STR2.len() as u64);
    let mut file = root_dir.open_file("moved-file.txt").unwrap();
    let mut buf = Vec::new();
    file.read_to_end(&mut buf).unwrap();
    assert_eq!(str::from_utf8(&buf).unwrap(), TEST_STR2);

    assert!(root_dir.rename("moved-file.txt", &root_dir, "short.txt").is_err());
    let entries = root_dir.iter().map(|r| r.unwrap()).collect::<Vec<_>>();
    let names = entries.iter().map(|r| r.file_name()).collect::<Vec<_>>();
    assert_eq!(
        names,
        ["long.txt", "short.txt", "very", "very-long-dir-name", "moved-file.txt"]
    );

    assert!(root_dir.rename("moved-file.txt", &root_dir, "moved-file.txt").is_ok());

    let new_stats = fs.stats().unwrap();
    assert_eq!(new_stats.free_clusters(), stats.free_clusters());
}

#[test]
fn test_rename_file_fat12() {
    call_with_fs(test_rename_file, FAT12_IMG, 6)
}

#[test]
fn test_rename_file_fat16() {
    call_with_fs(test_rename_file, FAT16_IMG, 6)
}

#[test]
fn test_rename_file_fat32() {
    call_with_fs(test_rename_file, FAT32_IMG, 6)
}

fn test_dirty_flag(tmp_path: &str) {
    // Open filesystem, make change, and forget it - should become dirty
    let fs = open_filesystem_rw(tmp_path);
    let status_flags = fs.read_status_flags().unwrap();
    assert!(!status_flags.dirty());
    assert!(!status_flags.io_error());
    fs.root_dir().create_file("abc.txt").unwrap();
    mem::forget(fs);
    // Check if volume is dirty now
    let fs = open_filesystem_rw(tmp_path);
    let status_flags = fs.read_status_flags().unwrap();
    assert!(status_flags.dirty());
    assert!(!status_flags.io_error());
    fs.unmount().unwrap();
    // Make sure remounting does not clear the dirty flag
    let fs = open_filesystem_rw(tmp_path);
    let status_flags = fs.read_status_flags().unwrap();
    assert!(status_flags.dirty());
    assert!(!status_flags.io_error());
}

#[test]
fn test_dirty_flag_fat12() {
    call_with_tmp_img(test_dirty_flag, FAT12_IMG, 7)
}

#[test]
fn test_dirty_flag_fat16() {
    call_with_tmp_img(test_dirty_flag, FAT16_IMG, 7)
}

#[test]
fn test_dirty_flag_fat32() {
    call_with_tmp_img(test_dirty_flag, FAT32_IMG, 7)
}

fn test_multiple_files_in_directory(fs: FileSystem) {
    let dir = fs.root_dir().create_dir("/TMP").unwrap();
    for i in 0..8 {
        let name = format!("T{}.TXT", i);
        let mut file = dir.create_file(&name).unwrap();
        file.write_all(TEST_STR.as_bytes()).unwrap();
        file.flush().unwrap();

        let file = dir.iter().map(|r| r.unwrap()).find(|e| e.file_name() == name).unwrap();

        assert_eq!(TEST_STR.len() as u64, file.len(), "Wrong file len on iteration {}", i);
    }
}

#[test]
fn test_multiple_files_in_directory_fat12() {
    call_with_fs(test_multiple_files_in_directory, FAT12_IMG, 8)
}

#[test]
fn test_multiple_files_in_directory_fat16() {
    call_with_fs(test_multiple_files_in_directory, FAT16_IMG, 8)
}

#[test]
fn test_multiple_files_in_directory_fat32() {
    call_with_fs(test_multiple_files_in_directory, FAT32_IMG, 8)
}
