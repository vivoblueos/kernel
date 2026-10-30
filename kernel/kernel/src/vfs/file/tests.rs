// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
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

use super::*;
use crate::vfs::{fs::FileSystem, inode::InodeOps, inode_mode::InodeMode, tmpfs::TmpFileSystem};
use blueos_test_macro::test;

fn tmp_file(data: &[u8], access: AccessMode) -> (Arc<TmpFileSystem>, File) {
    let fs = TmpFileSystem::new();
    let inode = fs
        .root_inode()
        .create(
            "positional",
            InodeFileType::Regular,
            InodeMode::from_bits_truncate(0o600),
        )
        .unwrap();
    assert_eq!(inode.write_at(0, data, false).unwrap(), data.len());
    let file = File::new(Dcache::new_root(inode), access, OpenFlags::empty()).unwrap();
    (fs, file)
}

// Keep real tmpfs attributes, but control reads to exercise short I/O and errors.
struct ReadInode {
    inner: Arc<dyn InodeOps>,
    read: fn(usize, &mut [u8], bool) -> Result<usize, Error>,
}

impl InodeOps for ReadInode {
    fn read_at(&self, offset: usize, dst: &mut [u8], nonblock: bool) -> Result<usize, Error> {
        (self.read)(offset, dst, nonblock)
    }

    delegate! {
        to self.inner {
            fn fs(&self) -> Option<Arc<dyn FileSystem>>;
            fn ino(&self) -> InodeNo;
            fn type_(&self) -> InodeFileType;
            fn inode_attr(&self) -> InodeAttr;
            fn file_attr(&self) -> FileAttr;
            fn mode(&self) -> InodeMode;
            fn size(&self) -> usize;
            fn atime(&self) -> Duration;
            fn set_atime(&self, time: Duration);
            fn mtime(&self) -> Duration;
            fn set_mtime(&self, time: Duration);
        }
    }
}

fn with_reader(file: &File, read: fn(usize, &mut [u8], bool) -> Result<usize, Error>) -> File {
    let inode = Arc::new(ReadInode {
        inner: file.dcache.inode().clone(),
        read,
    });
    File::new(
        Dcache::new_root(inode),
        file.access_mode(),
        file.open_flags(),
    )
    .unwrap()
}

#[test]
fn positional_reads_preserve_shared_offset() {
    let (_fs, file) = tmp_file(b"abcdefgh", AccessMode::O_RDWR);
    let file = Arc::new(file);
    let shared = file.clone();
    file.seek(SeekFrom::Start(5)).unwrap();

    let mut dst = [0; 3];
    assert_eq!(shared.read_at(1, &mut dst).unwrap(), 3);
    assert_eq!(&dst, b"bcd");
    shared.read_exact_at(2, &mut dst).unwrap();
    assert_eq!(&dst, b"cde");
    assert_eq!(file.offset(), 5);

    assert_eq!(file.read(&mut dst).unwrap(), 3);
    assert_eq!(&dst, b"fgh");
    assert_eq!(shared.offset(), 8);
}

#[test]
fn positional_reads_report_eof_without_moving_offset() {
    let (_fs, file) = tmp_file(b"abc", AccessMode::O_RDONLY);
    file.seek(SeekFrom::Start(1)).unwrap();
    let mut dst = [0; 4];
    assert_eq!(file.read_at(2, &mut dst).unwrap(), 1);
    assert_eq!(dst[0], b'c');
    assert_eq!(file.read_at(3, &mut dst).unwrap(), 0);
    assert_eq!(file.read_at(10, &mut dst).unwrap(), 0);
    assert_eq!(file.read_exact_at(0, &mut dst), Err(code::ENODATA));
    assert_eq!(&dst[..3], b"abc");
    assert_eq!(file.read_exact_at(3, &mut dst), Err(code::ENODATA));
    assert_eq!(file.offset(), 1);
}

#[test]
fn positional_reads_reject_write_only_files() {
    let (_fs, file) = tmp_file(b"abc", AccessMode::O_WRONLY);
    let file = with_reader(&file, |_, _, _| panic!("write-only read reached inode"));
    let mut dst = [0; 1];
    assert_eq!(file.read_at(0, &mut dst), Err(code::EACCES));
    assert_eq!(file.read_exact_at(0, &mut dst), Err(code::EACCES));
    assert_eq!(file.read_at(0, &mut []), Err(code::EACCES));
    assert_eq!(file.read_exact_at(0, &mut []), Err(code::EACCES));
    assert_eq!(file.offset(), 0);
}

#[test]
fn positional_reads_accept_empty_buffers() {
    let (_fs, file) = tmp_file(b"abc", AccessMode::O_RDONLY);
    file.seek(SeekFrom::Start(1)).unwrap();
    assert_eq!(file.read_at(3, &mut []).unwrap(), 0);
    assert_eq!(file.offset(), 1);
    let file = with_reader(&file, |_, _, _| panic!("empty exact read reached inode"));
    file.read_exact_at(u64::MAX, &mut []).unwrap();
    assert_eq!(file.offset(), 0);
}

#[test]
fn exact_positional_read_retries_short_reads() {
    let (_fs, file) = tmp_file(b"abcdefgh", AccessMode::O_RDONLY);
    let file = with_reader(&file, |offset, dst, nonblock| {
        assert!(!nonblock);
        let data = b"abcdefgh";
        let n = dst.len().min(2).min(data.len().saturating_sub(offset));
        dst[..n].copy_from_slice(&data[offset..offset + n]);
        Ok(n)
    });
    file.seek(SeekFrom::Start(7)).unwrap();
    let mut dst = [0; 5];
    file.read_exact_at(1, &mut dst).unwrap();
    assert_eq!(&dst, b"bcdef");
    assert_eq!(file.offset(), 7);
}

#[test]
fn positional_reads_forward_nonblock_and_errors() {
    let (_fs, file) = tmp_file(b"abc", AccessMode::O_RDONLY);
    let file = with_reader(&file, |offset, dst, nonblock| {
        if nonblock {
            if offset == 0 {
                dst[0] = b'a';
                return Ok(1);
            }
            Err(code::EAGAIN)
        } else {
            Err(code::EIO)
        }
    });
    file.seek(SeekFrom::Start(2)).unwrap();
    let mut dst = [0; 3];
    assert_eq!(file.read_at(0, &mut dst), Err(code::EIO));
    assert_eq!(file.read_exact_at(0, &mut dst), Err(code::EIO));
    file.set_open_flags(OpenFlags::O_NONBLOCK);
    assert_eq!(file.read_at(1, &mut dst), Err(code::EAGAIN));
    assert_eq!(file.read_exact_at(0, &mut dst), Err(code::EAGAIN));
    assert_eq!(dst[0], b'a');
    assert_eq!(file.offset(), 2);
}

#[test]
fn file_len_tracks_writes_and_truncation() {
    let (_fs, file) = tmp_file(b"", AccessMode::O_RDWR);
    assert_eq!(file.file_len().unwrap(), 0);
    assert_eq!(file.write(b"abcdef").unwrap(), 6);
    assert_eq!(file.file_len().unwrap(), 6);
    file.resize(2).unwrap();
    assert_eq!(file.file_len().unwrap(), 2);
    assert_eq!(file.offset(), 6);
}

#[cfg(target_pointer_width = "32")]
#[test]
fn positional_reads_reject_unrepresentable_offsets() {
    let (_fs, file) = tmp_file(b"", AccessMode::O_RDONLY);
    let file = with_reader(&file, |_, _, _| panic!("overflowing offset reached inode"));
    file.seek(SeekFrom::Start(1)).unwrap();
    let offset = u64::from(u32::MAX) + 1;
    assert_eq!(file.read_at(offset, &mut [0]), Err(code::EOVERFLOW));
    assert_eq!(file.read_exact_at(offset, &mut [0]), Err(code::EOVERFLOW));
    assert_eq!(file.offset(), 1);
}

#[cfg(target_pointer_width = "64")]
#[test]
fn exact_positional_read_rejects_offset_addition_overflow() {
    let (_fs, file) = tmp_file(b"", AccessMode::O_RDONLY);
    let file = with_reader(&file, |offset, dst, _| {
        assert_eq!(offset, usize::MAX);
        dst[0] = b'x';
        Ok(1)
    });
    file.seek(SeekFrom::Start(1)).unwrap();
    let mut dst = [0; 2];
    assert_eq!(file.read_exact_at(u64::MAX, &mut dst), Err(code::EOVERFLOW));
    assert_eq!(dst[0], b'x');
    assert_eq!(file.offset(), 1);
}
