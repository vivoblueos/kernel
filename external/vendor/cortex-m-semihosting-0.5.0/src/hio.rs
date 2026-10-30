//! Host I/O

use crate::nr;
use core::{fmt, slice};

/// A byte stream to the host (e.g., host's stdout or stderr).
#[derive(Clone, Copy)]
pub struct HostStream {
    fd: usize,
}

impl HostStream {
    /// Attempts to write an entire `buffer` into this sink
    pub fn write_all(&mut self, buffer: &[u8]) -> Result<(), ()> {
        write_all(self.fd, buffer)
    }
}

impl fmt::Write for HostStream {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.write_all(s.as_bytes()).map_err(|_| fmt::Error)
    }
}

/// Construct a new handle to the host's standard error.
pub fn hstderr() -> Result<HostStream, ()> {
    // There is actually no stderr access in ARM Semihosting documentation. Use
    // convention used in libgloss.
    // See: libgloss/arm/syscalls.c, line 139.
    // https://sourceware.org/git/gitweb.cgi?p=newlib-cygwin.git;a=blob;f=libgloss/arm/syscalls.c#l139
    open(":tt\0", nr::open::W_APPEND)
}

/// Construct a new handle to the host's standard output.
pub fn hstdout() -> Result<HostStream, ()> {
    open(":tt\0", nr::open::W_TRUNC)
}

fn open(name: &str, mode: usize) -> Result<HostStream, ()> {
    let name = name.as_bytes();
    match unsafe { syscall!(OPEN, name.as_ptr(), mode, name.len() - 1) } as isize {
        -1 => Err(()),
        fd => Ok(HostStream { fd: fd as usize }),
    }
}

fn write_all(fd: usize, mut buffer: &[u8]) -> Result<(), ()> {
    while !buffer.is_empty() {
        match unsafe { syscall!(WRITE, fd, buffer.as_ptr(), buffer.len()) } {
            // Done
            0 => return Ok(()),
            // `n` bytes were not written
            n if n <= buffer.len() => {
                let offset = (buffer.len() - n) as isize;
                buffer = unsafe { slice::from_raw_parts(buffer.as_ptr().offset(offset), n) }
            }
            #[cfg(feature = "jlink-quirks")]
            // Error (-1) - should be an error but JLink can return -1, -2, -3,...
            // For good measure, we allow up to negative 15.
            n if n > 0xfffffff0 => return Ok(()),
            // Error
            _ => return Err(()),
        }
    }
    Ok(())
}
