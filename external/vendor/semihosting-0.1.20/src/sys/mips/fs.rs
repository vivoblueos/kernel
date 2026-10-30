// SPDX-License-Identifier: Apache-2.0 OR MIT

use core::ffi::CStr;

use super::{
    O_APPEND, O_CREAT, O_EXCL, O_RDONLY, O_RDWR, O_TRUNC, O_WRONLY, SeekWhence::SEEK_SET, errno,
    mips_fstat, mips_lseek, mips_open,
};
pub(crate) use super::{mips_fstat as metadata, mips_unlink as unlink, uhi_stat as Metadata};
use crate::{
    fd::{BorrowedFd, OwnedFd},
    io::{self, Error, Result},
};

#[allow(clippy::cast_possible_wrap)]
pub(crate) fn open(path: &CStr, options: &crate::fs::OpenOptions) -> Result<OwnedFd> {
    match (options.write, options.append) {
        (true, false) => {}
        (false, false) => {
            if options.truncate || options.create {
                return Err(Error::from_raw_os_error(errno::EINVAL));
            }
        }
        (_, true) => {
            if options.truncate {
                return Err(Error::from_raw_os_error(errno::EINVAL));
            }
        }
    }
    let access_mode = match (options.read, options.write, options.append) {
        (true, false, false) => O_RDONLY,
        (false, true, false) => O_WRONLY,
        (true, true, false) => O_RDWR,
        (false, _, true) => O_WRONLY | O_APPEND,
        (true, _, true) => O_RDWR | O_APPEND,
        (false, false, false) => return Err(Error::from_raw_os_error(errno::EINVAL)),
    };
    let creation_mode = match (options.create, options.truncate, options.create_new) {
        (false, false, false) => 0,
        (true, false, false) => O_CREAT,
        (false, true, false) => O_TRUNC,
        (true, true, false) => O_CREAT | O_TRUNC,
        (_, _, true) => O_CREAT | O_EXCL,
    };
    mips_open(path, access_mode | creation_mode, options.mode as i32)
}

// TODO: UHI doesn't provide Large-file support (LFS).
#[allow(clippy::cast_possible_wrap)]
pub(crate) fn seek(fd: BorrowedFd<'_>, pos: io::SeekFrom) -> Result<u64> {
    let (whence, offset) = match pos {
        io::SeekFrom::Start(pos) => (SEEK_SET, pos as i64),
        io::SeekFrom::End(offset) => {
            // (SEEK_END, offset) doesn't reject invalid offset
            let len = mips_fstat(fd)?.size();
            let pos = (len as i64).saturating_add(offset);
            if pos.is_negative() {
                return Err(Error::from_raw_os_error(errno::EINVAL));
            }
            (SEEK_SET, pos)
        } // io::SeekFrom::Current(offset) => (SEEK_CUR, offset),
    };
    // mips_lseek will fail even without this guard, but errno will not be set.
    let offset = isize::try_from(offset).map_err(|_| Error::from_raw_os_error(errno::EINVAL))?;
    Ok(unsafe { mips_lseek(fd, offset, whence)? as u64 })
}

impl Metadata {
    pub(crate) fn size(&self) -> u64 {
        self.st_size
    }
}

pub(crate) fn rename(_from: &CStr, _to: &CStr) -> Result<()> {
    Err(io::ErrorKind::Unsupported.into())
}
