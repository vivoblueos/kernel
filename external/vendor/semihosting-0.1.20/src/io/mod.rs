// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Traits, helpers, and type definitions for core I/O functionality.
//!
//! This module is a subset of the [`std::io`] module except that the stdio functions returns
//! the `Result`.
//!
//! [`std::io`]: https://doc.rust-lang.org/std/io/index.html

// Based on nightly-2025-02-19's std::io module.

// TODO: io utilities e.g., Cursor?

pub use self::error::{Error, ErrorKind, RawOsError, Result};
#[macro_use]
mod error;

mod impls;

#[cfg(feature = "stdio")]
pub use self::stdio::{IsTerminal, Stderr, Stdin, Stdout, stderr, stdin, stdout};
#[cfg(feature = "stdio")]
#[cfg_attr(docsrs, doc(cfg(feature = "stdio")))]
mod stdio;

use core::fmt;

const _: fn() = || {
    fn assert_dyn_compatibility<T: ?Sized>() {}
    assert_dyn_compatibility::<dyn Read>();
    assert_dyn_compatibility::<dyn Write>();
    assert_dyn_compatibility::<dyn Seek>();
};

pub(crate) fn default_read_exact<R: ?Sized + Read>(this: &mut R, mut buf: &mut [u8]) -> Result<()> {
    while !buf.is_empty() {
        match this.read(buf) {
            Ok(0) => break,
            Ok(n) => {
                buf = &mut buf[n..];
            }
            Err(ref e) if e.is_interrupted() => {}
            Err(e) => return Err(e),
        }
    }
    if buf.is_empty() { Ok(()) } else { Err(Error::READ_EXACT_EOF) }
}

/// The `no_std` subset of `std::io::Read`.
///
/// Unless explicitly stated otherwise, API contracts adhere to `std::io::Read`.
///
/// See [`std::io::Read` documentation][std] for details.
///
/// [std]: https://doc.rust-lang.org/std/io/trait.Read.html
pub trait Read {
    /// Pull some bytes from this source into the specified buffer, returning
    /// how many bytes were read.
    ///
    /// See [`std::io::Read::read` documentation][std] for details.
    ///
    /// [std]: https://doc.rust-lang.org/std/io/trait.Read.html#tymethod.read
    fn read(&mut self, buf: &mut [u8]) -> Result<usize>;

    // /// Read all bytes until EOF in this source, placing them into `buf`.
    // ///
    // /// See [`std::io::Read::read_to_end` documentation][std] for details.
    // ///
    // /// [std]: https://doc.rust-lang.org/std/io/trait.Read.html#method.read_to_end
    // #[cfg(feature = "alloc")]
    // #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    // fn read_to_end(&mut self, buf: &mut Vec<u8>) -> Result<usize> {
    //     default_read_to_end(self, buf)
    // }

    // /// Read all bytes until EOF in this source, appending them to `buf`.
    // ///
    // /// See [`std::io::Read::read_to_string` documentation][std] for details.
    // ///
    // /// [std]: https://doc.rust-lang.org/std/io/trait.Read.html#method.read_to_string
    // #[cfg(feature = "alloc")]
    // #[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
    // fn read_to_string(&mut self, buf: &mut String) -> Result<usize> {
    //     default_read_to_string(self, buf)
    // }

    /// Read the exact number of bytes required to fill `buf`.
    ///
    /// See [`std::io::Read::read_exact` documentation][std] for details.
    ///
    /// [std]: https://doc.rust-lang.org/std/io/trait.Read.html#method.read_exact
    fn read_exact(&mut self, buf: &mut [u8]) -> Result<()> {
        default_read_exact(self, buf)
    }
}

/// The `no_std` subset of `std::io::Write`.
///
/// Unless explicitly stated otherwise, API contracts adhere to `std::io::Write`.
///
/// See [`std::io::Write` documentation][std] for details.
///
/// [std]: https://doc.rust-lang.org/std/io/trait.Write.html
pub trait Write {
    /// Write a buffer into this writer, returning how many bytes were written.
    ///
    /// See [`std::io::Write::write` documentation][std] for details.
    ///
    /// [std]: https://doc.rust-lang.org/std/io/trait.Write.html#tymethod.write
    fn write(&mut self, buf: &[u8]) -> Result<usize>;

    /// Flush this output stream, ensuring that all intermediately buffered
    /// contents reach their destination.
    ///
    /// See [`std::io::Write::flush` documentation][std] for details.
    ///
    /// [std]: https://doc.rust-lang.org/std/io/trait.Write.html#tymethod.flush
    fn flush(&mut self) -> Result<()>;

    /// Attempts to write an entire buffer into this writer.
    ///
    /// See [`std::io::Write::write_all` documentation][std] for details.
    ///
    /// [std]: https://doc.rust-lang.org/std/io/trait.Write.html#method.write_all
    fn write_all(&mut self, mut buf: &[u8]) -> Result<()> {
        while !buf.is_empty() {
            match self.write(buf) {
                Ok(0) => return Err(Error::WRITE_ALL_EOF),
                Ok(n) => buf = &buf[n..],
                Err(ref e) if e.is_interrupted() => {}
                Err(e) => return Err(e),
            }
        }
        Ok(())
    }

    /// Writes a formatted string into this writer, returning any error
    /// encountered.
    ///
    /// See [`std::io::Write::write_fmt` documentation][std] for details.
    ///
    /// [std]: https://doc.rust-lang.org/std/io/trait.Write.html#method.write_fmt
    fn write_fmt(&mut self, f: fmt::Arguments<'_>) -> Result<()> {
        // Create a shim which translates a Write to a fmt::Write and saves
        // off I/O errors. instead of discarding them
        struct Adapter<'a, T: ?Sized> {
            inner: &'a mut T,
            error: Result<()>,
        }

        impl<T: ?Sized + Write> fmt::Write for Adapter<'_, T> {
            fn write_str(&mut self, s: &str) -> fmt::Result {
                match self.inner.write_all(s.as_bytes()) {
                    Ok(()) => Ok(()),
                    Err(e) => {
                        self.error = Err(e);
                        Err(fmt::Error)
                    }
                }
            }
        }

        let mut output = Adapter { inner: self, error: Ok(()) };
        match fmt::write(&mut output, f) {
            Ok(()) => Ok(()),
            Err(..) => {
                // check if the error came from the underlying `Write` or not
                if output.error.is_err() {
                    output.error
                } else {
                    // This shouldn't happen: the underlying stream did not error, but somehow
                    // the formatter still errored?
                    panic!(
                        "a formatting trait implementation returned an error when the underlying stream did not"
                    );
                }
            }
        }
    }
}

/// The `no_std` subset of `std::io::Seek`.
///
/// Unless explicitly stated otherwise, API contracts adhere to `std::io::Seek`.
///
/// See [`std::io::Seek` documentation][std] for details.
///
/// [std]: https://doc.rust-lang.org/std/io/trait.Seek.html
pub trait Seek {
    /// Seek to an offset, in bytes, in a stream.
    ///
    /// See [`std::io::Seek::seek` documentation][std] for details.
    ///
    /// [std]: https://doc.rust-lang.org/std/io/trait.Seek.html#tymethod.seek
    fn seek(&mut self, pos: SeekFrom) -> Result<u64>;

    /// Rewind to the beginning of a stream.
    ///
    /// This is a convenience method, equivalent to `seek(SeekFrom::Start(0))`.
    fn rewind(&mut self) -> Result<()> {
        self.seek(SeekFrom::Start(0))?;
        Ok(())
    }

    // /// Returns the current seek position from the start of the stream.
    // ///
    // /// This is equivalent to `self.seek(SeekFrom::Current(0))`.
    // fn stream_position(&mut self) -> Result<u64> {
    //     self.seek(SeekFrom::Current(0))
    // }

    // /// Seeks relative to the current position.
    // ///
    // /// This is equivalent to `self.seek(SeekFrom::Current(offset))` but
    // /// doesn't return the new position which can allow some implementations
    // /// such as [`BufReader`] to perform more efficient seeks.
    // fn seek_relative(&mut self, offset: i64) -> Result<()> {
    //     self.seek(SeekFrom::Current(offset))?;
    //     Ok(())
    // }
}

/// Enumeration of possible methods to seek within an I/O object.
///
/// It is used by the [`Seek`] trait.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum SeekFrom {
    /// Sets the offset to the provided number of bytes.
    Start(u64),
    /// Sets the offset to the size of this object plus the specified number of
    /// bytes.
    ///
    /// It is possible to seek beyond the end of an object, but it's an error to
    /// seek before byte 0.
    End(i64),
    // TODO: It appears that SeekFrom::Current cannot be implemented with APIs provided by Arm semihosting...
    // /// Sets the offset to the current position plus the specified number of
    // /// bytes.
    // ///
    // /// It is possible to seek beyond the end of an object, but it's an error to
    // /// seek before byte 0.
    // Current(i64),
}
