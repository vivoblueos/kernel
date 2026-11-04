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

//! vfs_fd.rs  

use crate::{
    error::{code, Error},
    vfs::{
        file::{FileOps, OpenFlags},
        path,
    },
};
use alloc::{sync::Arc, vec, vec::Vec};
use core::ffi::c_int;
use log::warn;

/// Standard file descriptors
pub const STDIN_FILENO: c_int = 0;
pub const STDOUT_FILENO: c_int = 1;
pub const STDERR_FILENO: c_int = 2;
/// First available file descriptor
pub const FIRST_FD: usize = 3;

/// File descriptor manager
pub struct FdManager {
    /// File descriptor table
    fds: Vec<Option<Arc<dyn FileOps>>>,
    /// Next available file descriptor
    next_fd: usize,
}

impl FdManager {
    /// Create new file descriptor manager
    pub fn new() -> Self {
        Self {
            fds: vec![None; FIRST_FD + 1],
            next_fd: FIRST_FD,
        }
    }

    pub fn init_stdio(&mut self) -> Result<(), Error> {
        let stdin = path::open_path("/dev/console", libc::O_RDONLY, 0o666)?;
        let stdout = path::open_path("/dev/console", libc::O_WRONLY, 0o666)?;
        let stderr = path::open_path("/dev/console", libc::O_WRONLY, 0o666)?;

        self.fds[STDIN_FILENO as usize] = Some(Arc::new(stdin));
        self.fds[STDOUT_FILENO as usize] = Some(Arc::new(stdout));
        self.fds[STDERR_FILENO as usize] = Some(Arc::new(stderr));

        Ok(())
    }

    /// The child's descriptor table for `fork(2)`.
    ///
    /// POSIX: the child inherits the parent's descriptors, and each inherited
    /// descriptor refers to the *same* open file description — so the cloned
    /// slots hold the same `Arc<dyn FileOps>` and share the file offset, while
    /// the table itself is a fresh vector. `close(3)` in the child therefore
    /// only drops the child's reference and leaves the parent's descriptor
    /// intact. (`F_SETFL` status flags are still stored per `File`, so they are
    /// not shared yet; that is a separate gap.)
    pub fn fork_copy(&self) -> Self {
        Self {
            fds: self.fds.clone(),
            next_fd: self.next_fd,
        }
    }

    /// Close every descriptor marked `FD_CLOEXEC`, as a successful `execve`
    /// must. The table keeps its shape so the surviving descriptors keep their
    /// numbers.
    pub fn close_on_exec(&mut self) {
        for slot in self.fds.iter_mut() {
            let cloexec = slot
                .as_ref()
                .map_or(false, |file| file.flags().contains(OpenFlags::O_CLOEXEC));
            if cloexec {
                *slot = None;
            }
        }
        let len = self.fds.len();
        let next = (FIRST_FD..len).find(|&fd| self.fds[fd].is_none());
        self.next_fd = match next {
            Some(fd) => fd,
            None => {
                // `alloc_fd` writes at `next_fd`, so it always has to point at
                // an existing slot.
                self.fds.push(None);
                self.fds.len() - 1
            }
        };
    }

    /// Allocate new file descriptor
    pub fn alloc_fd(&mut self, file: Arc<dyn FileOps>) -> c_int {
        let fd = self.next_fd;
        self.fds[fd] = Some(file);
        self.update_next_fd(fd);
        fd as c_int
    }

    /// Duplicate file descriptor
    pub fn dup_fd(&mut self, fd: c_int, minfd: c_int, close_on_exec: bool) -> Result<c_int, Error> {
        let Some(file) = self.get_file_ops(fd) else {
            return Err(code::EBADF);
        };

        // `F_DUPFD` wants the lowest free descriptor at or above `minfd`. A
        // negative minimum is EINVAL; casting it to `usize` first would turn
        // it into a huge index and grow the table to match.
        if minfd < 0 {
            return Err(code::EINVAL);
        }
        let mut new_fd = minfd as usize;
        // find minfd
        let len = self.fds.len();
        while new_fd < len && self.fds[new_fd].is_some() {
            new_fd += 1;
        }
        if new_fd >= len {
            // add capacity by std Vec, so we just +1
            self.fds.resize(new_fd + 1, None);
        }

        // do dup
        let file2 = file.dup(close_on_exec)?;
        self.fds[new_fd] = Some(file2);
        self.update_next_fd(new_fd);
        Ok(new_fd as c_int)
    }

    /// `dup2()`: make `newfd` a copy of `oldfd`, closing whatever it named.
    ///
    /// The two steps that `dup2` needs and `F_DUPFD` does not are placing the
    /// copy at an exact index and closing the old occupant. Both happen under
    /// one lock, so a concurrent `read`/`close` on the process's own table
    /// cannot observe `newfd` empty in between.
    pub fn dup2_fd(&mut self, oldfd: c_int, newfd: c_int) -> Result<c_int, Error> {
        // A negative target cannot be a descriptor; POSIX spells this `EBADF`.
        if newfd < 0 {
            return Err(code::EBADF);
        }
        let Some(file) = self.get_file_ops(oldfd) else {
            return Err(code::EBADF);
        };
        // Equal descriptors are a no-op, but only after `oldfd` proved valid.
        if oldfd == newfd {
            return Ok(newfd);
        }

        let dup = file.dup(false)?;
        let newfd = newfd as usize;
        let replaced = if newfd < self.fds.len() {
            self.fds[newfd].take()
        } else {
            self.fds.resize(newfd + 1, None);
            None
        };
        self.fds[newfd] = Some(dup);
        if newfd == self.next_fd {
            // The slot `alloc_fd` was about to hand out is now taken.
            self.update_next_fd(newfd);
        }
        if let Some(replaced) = replaced {
            // Closing the shadowed descriptor is part of `dup2`; a failure
            // here is not the caller's to act on (POSIX says so explicitly).
            replaced.close().ok();
        }
        Ok(newfd as c_int)
    }

    /// Free file descriptor
    pub fn free_fd(&mut self, fd: c_int) -> Result<(), Error> {
        // close stdio is allowed
        if fd as usize >= self.fds.len() {
            warn!("[fd] free_fd: Invalid fd: {}", fd);
            return Err(code::EBADF);
        }

        if self.fds[fd as usize].is_none() {
            warn!("[fd] free_fd: Fd {} not in use", fd);
            return Err(code::EBADF);
        }

        self.fds[fd as usize] = None;
        Ok(())
    }

    /// Get file operation
    pub fn get_file_ops(&self, fd: c_int) -> Option<Arc<dyn FileOps>> {
        if fd < 0 || fd as usize >= self.fds.len() {
            warn!("[fd] get_file_ops: Invalid fd: {}", fd);
            return None;
        }

        match self.fds[fd as usize].as_ref() {
            Some(file) => Some(file.clone()),
            None => {
                warn!("[fd] get_file_ops: Fd {} not found", fd);
                None
            }
        }
    }

    /// Check if file descriptor is valid
    pub fn is_valid_fd(&self, fd: c_int) -> bool {
        fd >= 0 && (fd as usize) < self.fds.len() && self.fds[fd as usize].is_some()
    }

    /// Get current number of allocated file descriptors
    pub fn count(&self) -> usize {
        self.fds.iter().filter(|fd| fd.is_some()).count()
    }

    fn update_next_fd(&mut self, new_fd: usize) {
        let fds_len = self.fds.len();
        // First try: find free fd from new_fd+1 to end
        let next_fd = (new_fd + 1..fds_len)
            .find(|&fd| self.fds[fd].is_none())
            .unwrap_or_else(|| {
                // Second try: find free fd from start to new_fd
                (FIRST_FD..new_fd)
                    .find(|&fd| self.fds[fd].is_none())
                    .unwrap_or(fds_len) // If still not found, use fds_len
            });

        // Extend array if needed
        if next_fd >= fds_len {
            self.fds.resize(next_fd + 1, None);
        }

        self.next_fd = next_fd;
    }
}
