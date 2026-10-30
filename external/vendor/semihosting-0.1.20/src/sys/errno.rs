// SPDX-License-Identifier: Apache-2.0 OR MIT

use crate::{
    io::{self, RawOsError},
    sys::arch::errno,
};

#[inline]
pub(crate) fn is_interrupted(errno: i32) -> bool {
    errno == errno::EINTR
}

// From https://github.com/rust-lang/rust/blob/1.84.0/library/std/src/sys/pal/unix/mod.rs#L245.
pub(crate) fn decode_error_kind(errno: RawOsError) -> io::ErrorKind {
    #[allow(clippy::enum_glob_use)]
    use io::ErrorKind::*;
    match errno {
        #[cfg(not(any(
            target_arch = "mips",
            target_arch = "mips32r6",
            target_arch = "mips64",
            target_arch = "mips64r6",
        )))] // TODO
        errno::E2BIG => ArgumentListTooLong,
        // errno::EADDRINUSE => AddrInUse,
        // errno::EADDRNOTAVAIL => AddrNotAvailable,
        errno::EBUSY => ResourceBusy,
        // errno::ECONNABORTED => ConnectionAborted,
        // errno::ECONNREFUSED => ConnectionRefused,
        #[cfg(any(
            target_arch = "mips",
            target_arch = "mips32r6",
            target_arch = "mips64",
            target_arch = "mips64r6",
        ))] // TODO
        errno::ECONNRESET => ConnectionReset,
        // errno::EDEADLK => Deadlock,
        // errno::EDQUOT => QuotaExceeded,
        errno::EEXIST => AlreadyExists,
        errno::EFBIG => FileTooLarge,
        // errno::EHOSTUNREACH => HostUnreachable,
        errno::EINTR => Interrupted,
        errno::EINVAL => InvalidInput,
        errno::EISDIR => IsADirectory,
        // errno::ELOOP => FilesystemLoop, // unstable
        errno::ENOENT => NotFound,
        errno::ENOMEM => OutOfMemory,
        errno::ENOSPC => StorageFull,
        // errno::ENOSYS => Unsupported,
        errno::EMLINK => TooManyLinks,
        // errno::ENAMETOOLONG => InvalidFilename,
        // errno::ENETDOWN => NetworkDown,
        // errno::ENETUNREACH => NetworkUnreachable,
        #[cfg(any(
            target_arch = "mips",
            target_arch = "mips32r6",
            target_arch = "mips64",
            target_arch = "mips64r6",
        ))] // TODO
        errno::ENOTCONN => NotConnected,
        errno::ENOTDIR => NotADirectory,
        // errno::ENOTEMPTY => DirectoryNotEmpty,
        errno::EPIPE => BrokenPipe,
        errno::EROFS => ReadOnlyFilesystem,
        errno::ESPIPE => NotSeekable,
        // errno::ESTALE => StaleNetworkFileHandle,
        #[cfg(any(
            target_arch = "mips",
            target_arch = "mips32r6",
            target_arch = "mips64",
            target_arch = "mips64r6",
        ))] // TODO
        errno::ETIMEDOUT => TimedOut,
        // errno::ETXTBSY => ExecutableFileBusy,
        errno::EXDEV => CrossesDevices,
        // errno::EINPROGRESS => InProgress, // unstable
        errno::EACCES | errno::EPERM => PermissionDenied,

        // These two constants can have the same value on some systems,
        // but different values on others, so we can't use a match
        // clause
        #[cfg(any(
            target_arch = "mips",
            target_arch = "mips32r6",
            target_arch = "mips64",
            target_arch = "mips64r6",
        ))] // TODO
        x if x == errno::EAGAIN || x == errno::EWOULDBLOCK => WouldBlock,
        _ => Other,
    }
}
