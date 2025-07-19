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
//
// This code is based on relibc (original license follows):
// https://github.com/redox-os/relibc/blob/master/LICENSE
// standard MIT license

use alloc::boxed::Box;

use super::{constants::*, Buffer, FILE};
use crate::{
    c_str::CStr,
    errno::{Errno, ERRNO},
    fcntl::*,
    io::{self, BufWriter, Read, Seek, Write},
    string::strchr,
    sync::GenericMutex,
};
use alloc::vec::Vec;
use blueos_header::syscalls::NR::{Lseek, Open};
use blueos_scal::bk_syscall;
use core::{fmt, ops::Deref, ptr};
use libc::{
    c_char, c_int, c_ulonglong, c_void, off_t, size_t, EINVAL, FD_CLOEXEC, F_GETFL, F_SETFD,
    F_SETFL, O_APPEND, O_CLOEXEC, O_CREAT, O_EXCL, O_RDONLY, O_RDWR, O_TRUNC, O_WRONLY, SEEK_CUR,
    SEEK_END, SEEK_SET,
};

use crate::unistd::{close, io::write as unistd_write, read};
/// Parse mode flags as a string and output a mode flags integer
pub unsafe fn parse_mode_flags(mode_str: *const c_char) -> i32 {
    let mut flags = if !strchr(mode_str, b'+' as i32).is_null() {
        O_RDWR
    } else if (*mode_str) == b'r' as i8 {
        O_RDONLY
    } else {
        O_WRONLY
    };
    if !strchr(mode_str, b'x' as i32).is_null() {
        flags |= O_EXCL;
    }
    if !strchr(mode_str, b'e' as i32).is_null() {
        flags |= O_CLOEXEC;
    }
    if (*mode_str) != b'r' as i8 {
        flags |= O_CREAT;
    }
    if (*mode_str) == b'w' as i8 {
        flags |= O_TRUNC;
    } else if (*mode_str) == b'a' as i8 {
        flags |= O_APPEND;
    }

    flags
}

/// Open a file with the file descriptor `fd` in the mode `mode`
pub unsafe fn _fdopen(fd: c_int, mode: *const c_char) -> Option<*mut FILE> {
    if *mode != b'r' as i8 && *mode != b'w' as i8 && *mode != b'a' as i8 {
        ERRNO.set(EINVAL);
        return None;
    }

    let mut flags = 0;
    if strchr(mode, b'+' as i32).is_null() {
        flags |= if *mode == b'r' as i8 { F_NOWR } else { F_NORD };
    }

    if !strchr(mode, b'e' as i32).is_null() {
        fcntl(fd, F_SETFD, FD_CLOEXEC as c_ulonglong);
    }

    if *mode == 'a' as i8 {
        let f = fcntl(fd, F_GETFL, 0);
        if (f & O_APPEND) == 0 {
            fcntl(fd, F_SETFL, (f | O_APPEND) as c_ulonglong);
        }
        flags |= F_APP;
    }

    let file = File::new(fd);
    let writer = Box::new(BufWriter::new(file.get_ref()));

    Some(Box::into_raw(Box::new(FILE {
        lock: GenericMutex::new(()),

        file,
        flags,
        read_buf: Buffer::Owned(vec![0; BUFSIZ as usize]),
        read_pos: 0,
        read_size: 0,
        unget: Vec::new(),
        writer,
        orientation: 0,
    })))
}

pub struct File {
    pub fd: c_int,
    /// To avoid self referential FILE struct that needs both a reader and a writer,
    /// make "reference" files that share fd but don't close on drop.
    pub reference: bool,
}

impl File {
    pub fn new(fd: c_int) -> Self {
        Self {
            fd,
            reference: false,
        }
    }

    pub fn open(path: CStr, oflag: c_int) -> Result<Self, Errno> {
        // NOTE: just use blueos syscall, it's internal function
        // we won't adpat internal interface
        let fd = bk_syscall!(Open, path.as_ptr(), oflag, 0) as c_int;
        if fd < 0 {
            return Err(Errno(fd));
        }
        Ok(Self::new(fd))
    }
    /// Create a new file pointing to the same underlying descriptor. This file
    /// will know it's a "reference" and won't close the fd. It will, however,
    /// not prevent the original file from closing the fd.
    pub unsafe fn get_ref(&self) -> Self {
        Self {
            fd: self.fd,
            reference: true,
        }
    }
}

impl Read for &File {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let err = unsafe { read(self.fd, buf.as_ptr() as *const c_void, buf.len() as size_t) };
        match err {
            -1 => Err(io::last_os_error()),
            len => Ok(len as usize),
        }
    }
}

impl io::Write for &File {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let err = unistd_write(self.fd, buf.as_ptr() as *mut u8, buf.len());
        match err {
            -1 => Err(io::last_os_error()),
            len => Ok(len as usize),
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl Seek for &File {
    fn seek(&mut self, pos: io::SeekFrom) -> io::Result<u64> {
        let (offset, whence) = match pos {
            io::SeekFrom::Start(start) => (start as off_t, SEEK_SET),
            io::SeekFrom::Current(current) => (current as off_t, SEEK_CUR),
            io::SeekFrom::End(end) => (end as off_t, SEEK_END),
        };
        // NOTE: just use blueos syscall, it's internal function
        // we won't adpat internal interface
        Ok(bk_syscall!(Lseek, self.fd, offset as usize, whence) as u64)
    }
}

impl Read for File {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        (&mut &*self).read(buf)
    }
}

impl Write for File {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        (&mut &*self).write(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        (&mut &*self).flush()
    }
}

impl Seek for File {
    fn seek(&mut self, pos: io::SeekFrom) -> io::Result<u64> {
        (&mut &*self).seek(pos)
    }
}

impl Deref for File {
    type Target = c_int;

    fn deref(&self) -> &Self::Target {
        &self.fd
    }
}

impl Drop for File {
    fn drop(&mut self) {
        if !self.reference {
            let _ = close(self.fd);
        }
    }
}

pub trait WriteByte: fmt::Write {
    fn write_u8(&mut self, byte: u8) -> fmt::Result;
}

impl<W: WriteByte> WriteByte for &'_ mut W {
    fn write_u8(&mut self, byte: u8) -> fmt::Result {
        (**self).write_u8(byte)
    }
}
pub struct CountingWriter<T> {
    pub inner: T,
    pub written: usize,
}
impl<T> CountingWriter<T> {
    pub fn new(writer: T) -> Self {
        Self {
            inner: writer,
            written: 0,
        }
    }
}
impl<T: fmt::Write> fmt::Write for CountingWriter<T> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.written += s.len();
        self.inner.write_str(s)
    }
}
impl<T: WriteByte> WriteByte for CountingWriter<T> {
    fn write_u8(&mut self, byte: u8) -> fmt::Result {
        self.written += 1;
        self.inner.write_u8(byte)
    }
}
impl<T: io::Write> io::Write for CountingWriter<T> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let res = self.inner.write(buf);
        if let Ok(written) = res {
            self.written += written;
        }
        res
    }
    fn write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        match self.inner.write_all(buf) {
            Ok(()) => (),
            Err(ref err) if err.kind() == io::ErrorKind::WriteZero => (),
            Err(err) => return Err(err),
        }
        self.written += buf.len();
        Ok(())
    }
    fn flush(&mut self) -> io::Result<()> {
        self.inner.flush()
    }
}

pub struct StringWriter(pub *mut u8, pub usize);

impl Write for StringWriter {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        if self.1 > 1 {
            let copy_size = buf.len().min(self.1 - 1);
            unsafe {
                ptr::copy_nonoverlapping(buf.as_ptr(), self.0, copy_size);
                self.1 -= copy_size;

                self.0 = self.0.add(copy_size);
                *self.0 = 0;
            }
        }

        // Pretend the entire slice was written. This is because many functions
        // (like snprintf) expects a return value that reflects how many bytes
        // *would have* been written. So keeping track of this information is
        // good, and then if we want the *actual* written size we can just go
        // `cmp::min(written, maxlen)`.
        Ok(buf.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl fmt::Write for StringWriter {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        // can't fail
        self.write(s.as_bytes()).unwrap();
        Ok(())
    }
}
impl WriteByte for StringWriter {
    fn write_u8(&mut self, byte: u8) -> fmt::Result {
        // can't fail
        self.write(&[byte]).unwrap();
        Ok(())
    }
}

// pub struct Errno(pub c_int);
pub struct FileWriter(pub c_int, Option<Errno>);

impl FileWriter {
    pub fn new(fd: c_int) -> Self {
        Self(fd, None)
    }

    pub fn write(&mut self, buf: &[u8]) -> fmt::Result {
        let err = unistd_write(self.0, buf.as_ptr() as *mut u8, buf.len()) as c_int;
        if err < 0 {
            self.1 = Some(Errno(err));
        }
        Ok(())
    }
}

impl fmt::Write for FileWriter {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        let _ = self.write(s.as_bytes());
        Ok(())
    }
}

impl WriteByte for FileWriter {
    fn write_u8(&mut self, byte: u8) -> fmt::Result {
        let _ = self.write(&[byte]);
        Ok(())
    }
}

pub struct UnsafeStringWriter(pub *mut u8);
impl Write for UnsafeStringWriter {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        unsafe {
            ptr::copy_nonoverlapping(buf.as_ptr(), self.0, buf.len());
            self.0 = self.0.add(buf.len());
            *self.0 = b'\0';
        }
        Ok(buf.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
impl fmt::Write for UnsafeStringWriter {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        // can't fail
        self.write(s.as_bytes()).unwrap();
        Ok(())
    }
}
impl WriteByte for UnsafeStringWriter {
    fn write_u8(&mut self, byte: u8) -> fmt::Result {
        // can't fail
        self.write(&[byte]).unwrap();
        Ok(())
    }
}
