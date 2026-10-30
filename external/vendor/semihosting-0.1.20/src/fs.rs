// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Host filesystem manipulation operations.
//!
//! This module contains basic methods to manipulate the contents of the host filesystem.
//!
//! [`Path`] is not available in `core`, so this module uses [`CStr`] instead in the API where
//! `std` uses [`Path`]. When creating a path from a string literal, it is recommended to use the
//! C string literals (`c"..."`, available since Rust 1.77) or [c!](c!()) macro.
//!
//! ```no_run
//! use semihosting::{c, fs};
//!
//! // with C string literal
//! fs::write(c"a.txt", "abc")?;
//! // with c! macro
//! fs::write(c!("b.txt"), "123")?;
//! # Ok::<(), semihosting::io::Error>(())
//! ```
//!
//! This module is a subset of the [`std::fs`] module except that [`CStr`] is used for the path
//! instead of [`Path`].
//!
//! # Platform-specific behavior
//!
//! The operations provided by this module are mapped to the corresponding operations of the host
//! system. The details of its operation depend on the host system.
//!
//! [`std::fs`]: https://doc.rust-lang.org/std/fs/index.html
//! [`Path`]: https://doc.rust-lang.org/std/path/struct.Path.html

use core::{ffi::CStr, fmt};

use crate::{
    fd::{AsFd as _, OwnedFd},
    io::{self, Write as _},
    sys,
};

/// Write a slice as the entire contents of a file.
///
/// See [`std::fs::write` documentation][std] for details.
///
/// [std]: https://doc.rust-lang.org/std/fs/fn.write.html
pub fn write<P: AsRef<CStr>, C: AsRef<[u8]>>(path: P, contents: C) -> io::Result<()> {
    fn inner(path: &CStr, contents: &[u8]) -> io::Result<()> {
        File::create(path)?.write_all(contents)
    }
    inner(path.as_ref(), contents.as_ref())
}

/// Removes a file from the host filesystem.
///
/// See [`std::fs::remove_file` documentation][std] for details.
///
/// [std]: https://doc.rust-lang.org/std/fs/fn.remove_file.html
pub fn remove_file<P: AsRef<CStr>>(path: P) -> io::Result<()> {
    sys::fs::unlink(path.as_ref())
}

/// Rename a file or directory to a new name, replacing the original file if
/// `to` already exists.
///
/// See [`std::fs::rename` documentation][std] for details.
///
/// [std]: https://doc.rust-lang.org/std/fs/fn.rename.html
///
/// # Platform-specific behavior
///
/// Currently, this function is not supported on MIPS32/MIPS64.
pub fn rename<P: AsRef<CStr>, Q: AsRef<CStr>>(from: P, to: Q) -> io::Result<()> {
    sys::fs::rename(from.as_ref(), to.as_ref())
}

/// An object providing access to an open file on the host filesystem.
///
/// See [`std::fs::File` documentation][std] for details.
///
/// [std]: https://doc.rust-lang.org/std/fs/struct.File.html
pub struct File(OwnedFd);

impl File {
    /// Attempts to open a file in read-only mode.
    pub fn open<P: AsRef<CStr>>(path: P) -> io::Result<Self> {
        OpenOptions::new().read(true).open(path.as_ref())
    }
    /// Opens a file in write-only mode.
    pub fn create<P: AsRef<CStr>>(path: P) -> io::Result<Self> {
        OpenOptions::new().write(true).create(true).truncate(true).open(path.as_ref())
    }
    /// Returns a new OpenOptions object.
    #[must_use]
    pub fn options() -> OpenOptions {
        OpenOptions::new()
    }
    /// Queries metadata about the underlying file.
    pub fn metadata(&self) -> io::Result<Metadata> {
        sys::fs::metadata(self.as_fd()).map(Metadata)
    }
}

impl_as_fd!(File);
impl_from_fd!(File);
impl fmt::Debug for File {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("File").field("fd", &self.as_fd().as_raw_fd()).finish()
    }
}
impl io::Read for File {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        sys::read(self.as_fd(), buf)
    }
}
impl io::Write for File {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        sys::write(self.as_fd(), bytes)
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
impl io::Seek for File {
    fn seek(&mut self, pos: io::SeekFrom) -> io::Result<u64> {
        sys::fs::seek(self.as_fd(), pos)
    }
}
impl io::Read for &File {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        sys::read(self.as_fd(), buf)
    }
}
impl io::Write for &File {
    fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
        sys::write(self.as_fd(), bytes)
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
impl io::Seek for &File {
    fn seek(&mut self, pos: io::SeekFrom) -> io::Result<u64> {
        sys::fs::seek(self.as_fd(), pos)
    }
}

/// Options and flags which can be used to configure how a file is opened.
///
/// See [`std::fs::OpenOptions` documentation][std] for details.
///
/// [std]: https://doc.rust-lang.org/std/fs/struct.OpenOptions.html
#[derive(Clone, Debug)]
pub struct OpenOptions {
    // generic
    pub(crate) read: bool,
    pub(crate) write: bool,
    pub(crate) append: bool,
    pub(crate) truncate: bool,
    pub(crate) create: bool,
    #[allow(dead_code)]
    pub(crate) create_new: bool,
    // system-specific
    #[allow(dead_code)]
    pub(crate) mode: u32,
}

#[allow(missing_docs)] // TODO
impl OpenOptions {
    pub fn new() -> Self {
        Self {
            // generic
            read: false,
            write: false,
            append: false,
            truncate: false,
            create: false,
            create_new: false,
            // system-specific
            mode: 0o666,
        }
    }

    pub fn read(&mut self, read: bool) -> &mut Self {
        self.read = read;
        self
    }
    pub fn write(&mut self, write: bool) -> &mut Self {
        self.write = write;
        self
    }
    pub fn append(&mut self, append: bool) -> &mut Self {
        self.append = append;
        self
    }
    pub fn truncate(&mut self, truncate: bool) -> &mut Self {
        self.truncate = truncate;
        self
    }
    pub fn create(&mut self, create: bool) -> &mut Self {
        self.create = create;
        self
    }
    // pub fn create_new(&mut self, create_new: bool) {
    //     self.create_new = create_new;
    // }

    // pub fn custom_flags(&mut self, flags: i32) {
    //     self.custom_flags = flags;
    // }
    // pub fn mode(&mut self, mode: u32) {
    //     self.mode = mode as mode_t;
    // }

    pub fn open<P: AsRef<CStr>>(&self, path: P) -> io::Result<File> {
        sys::fs::open(path.as_ref(), self).map(File)
    }
}

/// Metadata information about a file.
pub struct Metadata(sys::fs::Metadata);

impl Metadata {
    /// Returns the size of the file, in bytes, this metadata is for.
    #[must_use]
    pub fn len(&self) -> u64 {
        self.0.size()
    }
}

impl fmt::Debug for Metadata {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Metadata").finish_non_exhaustive()
    }
}
