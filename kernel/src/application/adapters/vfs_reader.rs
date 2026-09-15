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

//! `ElfReader` adapter over an opened VFS file.
//!
//! [`VfsElfReader`] binds the loader's neutral [`ElfReader`] contract to a
//! concrete [`File`]. Positional reads leave the shared file offset untouched.

use crate::{
    error::{code, Error},
    vfs::File,
};
use blueos_loader::{ElfReader, ErrorContext, LoadError, LoadErrorKind, LoadResult};

/// A read-only ELF reader over an opened VFS file.
///
/// The reader holds the `File` by value and leaves `File.offset` untouched, so
/// two readers can interleave reads of the same inode without interference.
pub struct VfsElfReader {
    file: File,
}

impl VfsElfReader {
    /// Wrap an opened file for loader reads.
    pub fn new(file: File) -> Self {
        Self { file }
    }
}

impl ElfReader for VfsElfReader {
    fn len(&self) -> LoadResult<u64> {
        self.file
            .file_len()
            .map_err(|error| map_error(error, 0, 0, 0))
    }

    fn read_exact_at(&self, offset: u64, dst: &mut [u8]) -> LoadResult<()> {
        let len = u64::try_from(dst.len())
            .map_err(|_| LoadError::new(LoadErrorKind::IntegerOverflow, ErrorContext::None))?;
        let file_len = self.len()?;
        self.file
            .read_exact_at(offset, dst)
            .map_err(|error| map_error(error, offset, len, file_len))
    }
}

/// Classify a kernel VFS error into a stable loader error: a short
/// read at EOF maps to `OutOfBounds`, an offset overflow to
/// `IntegerOverflow`, a device I/O failure to `Io`, and anything else to
/// `Backend`.
fn map_error(error: Error, offset: u64, len: u64, file_len: u64) -> LoadError {
    let kind = if error == code::EIO {
        LoadErrorKind::Io
    } else if error == code::EOVERFLOW {
        LoadErrorKind::IntegerOverflow
    } else if error == code::ENODATA {
        LoadErrorKind::OutOfBounds
    } else {
        LoadErrorKind::Backend
    };
    LoadError::new(
        kind,
        ErrorContext::FileRange {
            offset,
            len,
            file_len,
        },
    )
}
