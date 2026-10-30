use std::fs;
use std::io::prelude::*;
use std::io::SeekFrom;
use std::str;

use fatfs::{FatType, FsOptions, StdIoWrapper};
use fscommon::BufStream;

const TEST_TEXT: &str = "Rust is cool!\n";
const FAT12_IMG: &str = "resources/fat12.img";
const FAT16_IMG: &str = "resources/fat16.img";
const FAT32_IMG: &str = "resources/fat32.img";

type FileSystem = fatfs::FileSystem<StdIoWrapper<BufStream<fs::File>>>;

fn call_with_fs<F: Fn(FileSystem)>(f: F, filename: &str) {
    let _ = env_logger::builder().is_test(true).try_init();
    let file = fs::File::open(filename).unwrap();
    let buf_file = BufStream::new(file);
    let fs = FileSystem::new(buf_file, FsOptions::new()).unwrap();
    f(fs);
}

fn test_root_dir(fs: FileSystem) {
    let root_dir = fs.root_dir();
    let entries = root_dir.iter().map(|r| r.unwrap()).collect::<Vec<_>>();
    let short_names = entries.iter().map(|e| e.short_file_name()).collect::<Vec<String>>();
    assert_eq!(short_names, ["LONG.TXT", "SHORT.TXT", "VERY", "VERY-L~1"]);
    let names = entries.iter().map(|e| e.file_name()).collect::<Vec<String>>();
    assert_eq!(names, ["long.txt", "short.txt", "very", "very-long-dir-name"]);
    // Try read again
    let names2 = root_dir.iter().map(|r| r.unwrap().file_name()).collect::<Vec<String>>();
    assert_eq!(names2, names);
}

#[test]
fn test_root_dir_fat12() {
    call_with_fs(test_root_dir, FAT12_IMG)
}

#[test]
fn test_root_dir_fat16() {
    call_with_fs(test_root_dir, FAT16_IMG)
}

#[test]
fn test_root_dir_fat32() {
    call_with_fs(test_root_dir, FAT32_IMG)
}

fn test_read_seek_short_file(fs: FileSystem) {
    let root_dir = fs.root_dir();
    let mut short_file = root_dir.open_file("short.txt").unwrap();
    let mut buf = Vec::new();
    short_file.read_to_end(&mut buf).unwrap();
    assert_eq!(str::from_utf8(&buf).unwrap(), TEST_TEXT);

    assert_eq!(short_file.seek(SeekFrom::Start(5)).unwrap(), 5);
    let mut buf2 = [0; 5];
    short_file.read_exact(&mut buf2).unwrap();
    assert_eq!(str::from_utf8(&buf2).unwrap(), &TEST_TEXT[5..10]);

    assert_eq!(short_file.seek(SeekFrom::Start(1000)).unwrap(), TEST_TEXT.len() as u64);
    let mut buf2 = [0; 5];
    assert_eq!(short_file.read(&mut buf2).unwrap(), 0);
}

#[test]
fn test_read_seek_short_file_fat12() {
    call_with_fs(test_read_seek_short_file, FAT12_IMG)
}

#[test]
fn test_read_seek_short_file_fat16() {
    call_with_fs(test_read_seek_short_file, FAT16_IMG)
}

#[test]
fn test_read_seek_short_file_fat32() {
    call_with_fs(test_read_seek_short_file, FAT32_IMG)
}

fn test_read_long_file(fs: FileSystem) {
    let root_dir = fs.root_dir();
    let mut long_file = root_dir.open_file("long.txt").unwrap();
    let mut buf = Vec::new();
    long_file.read_to_end(&mut buf).unwrap();
    assert_eq!(str::from_utf8(&buf).unwrap(), TEST_TEXT.repeat(1000));

    assert_eq!(long_file.seek(SeekFrom::Start(2017)).unwrap(), 2017);
    buf.clear();
    let mut buf2 = [0; 10];
    long_file.read_exact(&mut buf2).unwrap();
    assert_eq!(str::from_utf8(&buf2).unwrap(), &TEST_TEXT.repeat(1000)[2017..2027]);
}

#[test]
fn test_read_long_file_fat12() {
    call_with_fs(test_read_long_file, FAT12_IMG)
}

#[test]
fn test_read_long_file_fat16() {
    call_with_fs(test_read_long_file, FAT16_IMG)
}

#[test]
fn test_read_long_file_fat32() {
    call_with_fs(test_read_long_file, FAT32_IMG)
}

fn test_get_dir_by_path(fs: FileSystem) {
    let root_dir = fs.root_dir();
    let dir = root_dir.open_dir("very/long/path/").unwrap();
    let names = dir.iter().map(|r| r.unwrap().file_name()).collect::<Vec<String>>();
    assert_eq!(names, [".", "..", "test.txt"]);

    let dir2 = root_dir.open_dir("very/long/path/././.").unwrap();
    let names2 = dir2.iter().map(|r| r.unwrap().file_name()).collect::<Vec<String>>();
    assert_eq!(names2, [".", "..", "test.txt"]);

    let root_dir2 = root_dir.open_dir("very/long/path/../../..").unwrap();
    let root_names = root_dir2
        .iter()
        .map(|r| r.unwrap().file_name())
        .collect::<Vec<String>>();
    let root_names2 = root_dir.iter().map(|r| r.unwrap().file_name()).collect::<Vec<String>>();
    assert_eq!(root_names, root_names2);

    root_dir.open_dir("VERY-L~1").unwrap();
}

#[test]
fn test_get_dir_by_path_fat12() {
    call_with_fs(test_get_dir_by_path, FAT12_IMG)
}

#[test]
fn test_get_dir_by_path_fat16() {
    call_with_fs(test_get_dir_by_path, FAT16_IMG)
}

#[test]
fn test_get_dir_by_path_fat32() {
    call_with_fs(test_get_dir_by_path, FAT32_IMG)
}

fn test_get_file_by_path(fs: FileSystem) {
    let root_dir = fs.root_dir();
    let mut file = root_dir.open_file("very/long/path/test.txt").unwrap();
    let mut buf = Vec::new();
    file.read_to_end(&mut buf).unwrap();
    assert_eq!(str::from_utf8(&buf).unwrap(), TEST_TEXT);

    let mut file = root_dir
        .open_file("very-long-dir-name/very-long-file-name.txt")
        .unwrap();
    let mut buf = Vec::new();
    file.read_to_end(&mut buf).unwrap();
    assert_eq!(str::from_utf8(&buf).unwrap(), TEST_TEXT);

    root_dir.open_file("VERY-L~1/VERY-L~1.TXT").unwrap();

    // try opening dir as file
    assert!(root_dir.open_file("very/long/path").is_err());
    // try opening file as dir
    assert!(root_dir.open_dir("very/long/path/test.txt").is_err());
    // try using invalid path containing file as non-last component
    assert!(root_dir.open_file("very/long/path/test.txt/abc").is_err());
    assert!(root_dir.open_dir("very/long/path/test.txt/abc").is_err());
}

#[test]
fn test_get_file_by_path_fat12() {
    call_with_fs(test_get_file_by_path, FAT12_IMG)
}

#[test]
fn test_get_file_by_path_fat16() {
    call_with_fs(test_get_file_by_path, FAT16_IMG)
}

#[test]
fn test_get_file_by_path_fat32() {
    call_with_fs(test_get_file_by_path, FAT32_IMG)
}

fn test_volume_metadata(fs: FileSystem, fat_type: FatType) {
    assert_eq!(fs.volume_id(), 0x1234_5678);
    assert_eq!(fs.volume_label(), "Test!");
    assert_eq!(&fs.read_volume_label_from_root_dir().unwrap().unwrap(), "Test!");
    assert_eq!(fs.fat_type(), fat_type);
}

#[test]
fn test_volume_metadata_fat12() {
    call_with_fs(|fs| test_volume_metadata(fs, FatType::Fat12), FAT12_IMG)
}

#[test]
fn test_volume_metadata_fat16() {
    call_with_fs(|fs| test_volume_metadata(fs, FatType::Fat16), FAT16_IMG)
}

#[test]
fn test_volume_metadata_fat32() {
    call_with_fs(|fs| test_volume_metadata(fs, FatType::Fat32), FAT32_IMG)
}

fn test_status_flags(fs: FileSystem) {
    let status_flags = fs.read_status_flags().unwrap();
    assert!(!status_flags.dirty());
    assert!(!status_flags.io_error());
}

#[test]
fn test_status_flags_fat12() {
    call_with_fs(test_status_flags, FAT12_IMG)
}

#[test]
fn test_status_flags_fat16() {
    call_with_fs(test_status_flags, FAT16_IMG)
}

#[test]
fn test_status_flags_fat32() {
    call_with_fs(test_status_flags, FAT32_IMG)
}

#[test]
fn test_stats_fat12() {
    call_with_fs(
        |fs| {
            let stats = fs.stats().unwrap();
            assert_eq!(stats.cluster_size(), 512);
            assert_eq!(stats.total_clusters(), 1955); // 1000 * 1024 / 512 = 2000
            assert_eq!(stats.free_clusters(), 1920);
        },
        FAT12_IMG,
    )
}

#[test]
fn test_stats_fat16() {
    call_with_fs(
        |fs| {
            let stats = fs.stats().unwrap();
            assert_eq!(stats.cluster_size(), 512);
            assert_eq!(stats.total_clusters(), 4927); // 2500 * 1024 / 512 = 5000
            assert_eq!(stats.free_clusters(), 4892);
        },
        FAT16_IMG,
    )
}

#[test]
fn test_stats_fat32() {
    call_with_fs(
        |fs| {
            let stats = fs.stats().unwrap();
            assert_eq!(stats.cluster_size(), 512);
            assert_eq!(stats.total_clusters(), 66922); // 34000 * 1024 / 512 = 68000
            assert_eq!(stats.free_clusters(), 66886);
        },
        FAT32_IMG,
    )
}

#[test]
fn test_multi_thread() {
    call_with_fs(
        |fs| {
            use std::sync::{Arc, Mutex};
            use std::thread;
            let shared_fs = Arc::new(Mutex::new(fs));
            let mut handles = vec![];
            for _ in 0..2 {
                let shared_fs_cloned = Arc::clone(&shared_fs);
                let handle = thread::spawn(move || {
                    let fs2 = shared_fs_cloned.lock().unwrap();
                    assert_eq!(fs2.fat_type(), FatType::Fat32);
                });
                handles.push(handle);
            }
            for handle in handles {
                handle.join().unwrap();
            }
        },
        FAT32_IMG,
    )
}
