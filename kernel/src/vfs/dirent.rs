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

//! vfs_dirent.rs  

use crate::{
    error::{code, Error},
    support::align_up_size,
    vfs::inode_mode::InodeFileType,
};
use core::{
    ffi::{CStr, FromBytesUntilNulError},
    marker::PhantomData,
    mem::{align_of, offset_of, size_of, transmute},
};

/// File type enum
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum DirentType {
    Unknown = 0, // Unknown type
    Fifo = 1,    // Named pipe
    Chr = 2,     // Character device
    Dir = 4,     // Directory
    Blk = 6,     // Block device
    Reg = 8,     // Regular file
    Lnk = 10,    // Symbolic link
    Sock = 12,   // Socket
    Wht = 14,    // Reserved
}

impl From<InodeFileType> for DirentType {
    fn from(type_: InodeFileType) -> Self {
        match type_ {
            InodeFileType::Regular => DirentType::Reg,
            InodeFileType::Directory => DirentType::Dir,
            InodeFileType::SymLink => DirentType::Lnk,
            InodeFileType::CharDevice => DirentType::Chr,
            InodeFileType::BlockDevice => DirentType::Blk,
            InodeFileType::Socket => DirentType::Sock,
            InodeFileType::Fifo => DirentType::Fifo,
            InodeFileType::Unknown => DirentType::Unknown,
        }
    }
}

impl From<u8> for DirentType {
    fn from(value: u8) -> Self {
        unsafe { transmute(value) }
    }
}

#[derive(Debug, Clone)]
#[repr(C)]
pub struct Dirent {
    d_ino: usize,
    d_off: i64,
    /// The length of the dirent
    d_reclen: u16,
    /// The type of the file
    d_type: u8,
    // The file name - flexible array member
    d_name: [u8; 0],
}

crate::static_assert!(size_of::<Dirent>() == size_of::<libc::dirent>());
crate::static_assert!(align_of::<Dirent>() == align_of::<libc::dirent>());
crate::static_assert!(offset_of!(Dirent, d_name) == offset_of!(libc::dirent, d_name));

impl Dirent {
    pub const NAME_OFFSET: usize = offset_of!(Self, d_name);

    /// Create a new Dirent instance
    pub const fn new(ino: usize, off: i64, type_: DirentType, reclen: u16) -> Self {
        Self {
            d_ino: ino,
            d_off: off,
            d_reclen: reclen,
            d_type: type_ as u8,
            d_name: [],
        }
    }

    /// Get the inode number
    pub fn ino(&self) -> usize {
        self.d_ino
    }

    /// Get the offset
    pub fn off(&self) -> i64 {
        self.d_off
    }

    /// Get the file type
    pub fn type_(&self) -> DirentType {
        unsafe { transmute(self.d_type) }
    }

    /// Get the length of the dirent
    pub fn reclen(&self) -> u16 {
        self.d_reclen
    }

    /// Get the file name as a CStr
    pub fn name(&self) -> Result<&CStr, FromBytesUntilNulError> {
        let name_slice = unsafe {
            core::slice::from_raw_parts(
                (self as *const Self as *const u8).add(Self::NAME_OFFSET),
                256,
            )
        };
        CStr::from_bytes_until_nul(name_slice)
    }

    /// Get a reference to Dirent from a raw buffer
    pub unsafe fn from_buf_ref(buf: &[u8]) -> &Self {
        let ptr = buf.as_ptr() as *const Self;
        &*ptr
    }
}

pub struct DirBufferReader<'a> {
    buf: &'a mut [u8],
    read_pos: usize,
    _marker: PhantomData<&'a mut [u8]>,
}

impl<'a> DirBufferReader<'a> {
    pub fn new(buf: &'a mut [u8]) -> Self {
        Self {
            buf,
            read_pos: 0,
            _marker: PhantomData,
        }
    }

    pub fn write_node(
        &mut self,
        ino: usize,
        off: i64,
        type_: InodeFileType,
        name: &str,
    ) -> Result<(), Error> {
        let name_len = name.len().min(255);
        let dirent_size = align_up_size(Dirent::NAME_OFFSET + name_len + 1, align_of::<Dirent>());
        if self.read_pos + dirent_size > self.buf.len() {
            return Err(code::ENOMEM);
        }
        // write dirent
        let dir = Dirent::new(ino, off, DirentType::from(type_), dirent_size as u16);
        let dir_bytes: &[u8] = unsafe {
            core::slice::from_raw_parts(&dir as *const Dirent as *const u8, Dirent::NAME_OFFSET)
        };
        self.buf[self.read_pos..self.read_pos + Dirent::NAME_OFFSET].copy_from_slice(dir_bytes);

        let name_bytes = name.as_bytes();
        self.buf
            [self.read_pos + Dirent::NAME_OFFSET..self.read_pos + Dirent::NAME_OFFSET + name_len]
            .copy_from_slice(&name_bytes[..name_len]);
        self.buf[self.read_pos + Dirent::NAME_OFFSET + name_len] = 0;
        self.read_pos += dirent_size;

        Ok(())
    }

    pub fn recv_len(&self) -> usize {
        self.read_pos
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn test_dirent() {
        let mut buf = [0u8; 256];
        let mut reader = DirBufferReader::new(&mut buf);
        assert!(reader
            .write_node(1, 0, InodeFileType::Regular, "test.txt")
            .is_ok());
        let dirent = unsafe { Dirent::from_buf_ref(&buf) };
        assert_eq!(dirent.ino(), 1);
        assert_eq!(dirent.off(), 0);
        assert_eq!(dirent.type_(), DirentType::Reg);
        assert_eq!(
            dirent.reclen(),
            align_up_size(
                Dirent::NAME_OFFSET + "test.txt".len() + 1,
                align_of::<Dirent>()
            ) as u16
        );
        assert_eq!(dirent.name().unwrap().to_string_lossy(), "test.txt");
    }

    #[test]
    fn test_dirent_long_name() {
        let mut buf = [0u8; 1024];
        let mut reader = DirBufferReader::new(&mut buf);
        let long_name = "a".repeat(300);
        assert!(reader
            .write_node(1, 0, InodeFileType::Regular, &long_name)
            .is_ok());
        let dirent = unsafe { Dirent::from_buf_ref(&buf) };
        assert_eq!(dirent.name().unwrap().to_string_lossy().len(), 255);
    }

    #[test]
    fn test_dir_buffer_reader() {
        let mut buf = [0u8; 1024];
        let mut reader = DirBufferReader::new(&mut buf);

        assert!(reader
            .write_node(1, 0, InodeFileType::Regular, "test.txt")
            .is_ok());
        assert!(reader
            .write_node(2, 1, InodeFileType::Directory, "dir")
            .is_ok());

        // Test buffer overflow
        let mut small_buf = [0u8; 1];
        let mut reader = DirBufferReader::new(&mut small_buf);
        assert!(reader
            .write_node(1, 2, InodeFileType::Regular, "test.txt")
            .is_err());
    }
}
