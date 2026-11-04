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

//! Anonymous pipes (`pipe(2)`).
//!
//! A pipe is a bounded byte queue with two ends. The queue lives in
//! [`PipeBuffer`], shared by both endings, and each descriptor owns one
//! [`PipeEnd`]. The two ends count their own open descriptors: an `Arc<PipeEnd>`
//! is cloned by `dup()` *and* by `fork`, so a plain [`Drop`] is exactly the
//! "last descriptor for this end is closed" event the POSIX rules are written
//! in terms of — no separate reference counter to keep in step.
//!
//! Blocking uses the kernel's futex-style [`atomic_wait`]: every change to the
//! queue or to the end counts bumps [`PipeBuffer::epoch`], and a waiter samples
//! that counter before checking the condition. A change that lands between the
//! sample and the wait makes `atomic_wait` return immediately instead of
//! sleeping through it, so no wakeup is lost.
//!
//! What is deliberately not here: `SIGPIPE` (the kernel has no way to raise it
//! from a `FileOps` method), `F_SETPIPE_SZ`, and named pipes (`mkfifo` is
//! `ENOSYS` in the syscall layer). A write to a pipe whose read end is closed
//! reports `EPIPE` and lets libc decide what to do about the signal.

use crate::{
    error::{code, Error},
    sync::{atomic_wait::atomic_wait, SpinLock},
    time::Tick,
    vfs::{
        file::{FileAttr, FileOps, OpenFlags},
        inode_mode::{mode_t, InodeFileType},
        poll::{POLLERR, POLLHUP, POLLIN, POLLOUT},
    },
};
use alloc::{collections::VecDeque, sync::Arc};
use core::sync::atomic::{AtomicI32, AtomicUsize, Ordering};

/// Queue size, matching the power-of-two default Linux uses for new pipes.
///
/// The queue grows lazily up to this limit rather than reserving it up front:
/// most pipes in a shell pipeline carry far less, and the kernel heap is not
/// large enough to preallocate 64 KiB per pipe.
pub const PIPE_CAPACITY: usize = 65536;

/// State shared by both ends of one pipe.
struct PipeBuffer {
    /// Bytes written and not yet read, oldest first.
    data: SpinLock<VecDeque<u8>>,
    /// Open read ends. Reaches zero when every reader has closed.
    readers: AtomicUsize,
    /// Open write ends. Reaches zero when every writer has closed.
    writers: AtomicUsize,
    /// Bumped on every state change; the futex key for blocked readers/writers.
    epoch: AtomicUsize,
}

impl PipeBuffer {
    fn new() -> Self {
        Self {
            data: SpinLock::new(VecDeque::new()),
            readers: AtomicUsize::new(1),
            writers: AtomicUsize::new(1),
            epoch: AtomicUsize::new(0),
        }
    }

    /// Publish a state change to anyone blocked on this pipe.
    ///
    /// Callers bump while holding `data` (or before releasing it) so that a
    /// waiter either sees the new state in its re-check or sees the bumped
    /// epoch and does not sleep.
    fn bump(&self) {
        self.epoch.fetch_add(1, Ordering::Release);
        // A `poll()` blocked on this descriptor has no way to learn about a
        // pipe becoming readable/writable/hung up: it watches the process-wide
        // poll epoch, so that is what has to move.
        crate::vfs::poll::bump_poll_epoch();
    }
}

/// One descriptor's view of a pipe.
///
/// `write_end` selects the direction; a `FileOps` method for the wrong
/// direction answers `EBADF`, as POSIX requires for `read()` on a write end and
/// `write()` on a read end.
pub struct PipeEnd {
    buf: Arc<PipeBuffer>,
    write_end: bool,
    /// `O_NONBLOCK` plus `O_CLOEXEC`, exactly as `fcntl` reports them.
    flags: AtomicI32,
}

impl PipeEnd {
    fn access_bits(&self) -> i32 {
        if self.write_end {
            libc::O_WRONLY
        } else {
            libc::O_RDONLY
        }
    }

    fn is_nonblock(&self) -> bool {
        self.flags.load(Ordering::Relaxed) & libc::O_NONBLOCK != 0
    }

    /// Sleep until the pipe changes, given the epoch sampled *before* the
    /// caller's condition check.
    ///
    /// The sample has to be taken before the check, not after: a change that
    /// lands between the check and the wait would otherwise be counted into
    /// the "expected" value and the thread would sleep through it. Sampled
    /// first, every such change makes `atomic_wait` return `EAGAIN` instead of
    /// blocking, and the caller's loop re-tests.
    fn wait(&self, observed: usize) {
        let _ = atomic_wait(&self.buf.epoch, observed, Tick::MAX);
    }
}

impl FileOps for PipeEnd {
    fn read(&self, buf: &mut [u8]) -> Result<usize, Error> {
        if self.write_end {
            return Err(code::EBADF);
        }
        loop {
            // Sample before the check; see `wait`.
            let observed = self.buf.epoch.load(Ordering::Acquire);
            {
                let mut data = self.buf.data.lock();
                if !data.is_empty() {
                    let n = buf.len().min(data.len());
                    for slot in buf.iter_mut().take(n) {
                        // `is_empty` was false and `n <= len`, so this cannot
                        // be `None`.
                        *slot = data.pop_front().unwrap_or(0);
                    }
                    self.buf.bump();
                    return Ok(n);
                }
                // No data and no writer left: end of file. This is the only
                // way `read()` on a pipe returns 0.
                if self.buf.writers.load(Ordering::Acquire) == 0 {
                    return Ok(0);
                }
            }
            if self.is_nonblock() {
                return Err(code::EAGAIN);
            }
            self.wait(observed);
        }
    }

    fn write(&self, buf: &[u8]) -> Result<usize, Error> {
        if !self.write_end {
            return Err(code::EBADF);
        }
        loop {
            // Sample before the check; see `wait`.
            let observed = self.buf.epoch.load(Ordering::Acquire);
            {
                let mut data = self.buf.data.lock();
                if self.buf.readers.load(Ordering::Acquire) == 0 {
                    return Err(code::EPIPE);
                }
                let space = PIPE_CAPACITY - data.len();
                if space > 0 {
                    let n = buf.len().min(space);
                    data.extend(buf.iter().take(n).copied());
                    self.buf.bump();
                    return Ok(n);
                }
            }
            if self.is_nonblock() {
                return Err(code::EAGAIN);
            }
            self.wait(observed);
        }
    }

    fn dup(&self, close_on_exec: bool) -> Result<Arc<dyn FileOps>, Error> {
        // `dup()` creates a *second* `PipeEnd` object, so it is a second
        // `Drop`; the end count has to grow with it. `fork` clones the `Arc`
        // instead and therefore needs no adjustment here.
        if self.write_end {
            self.buf.writers.fetch_add(1, Ordering::AcqRel);
        } else {
            self.buf.readers.fetch_add(1, Ordering::AcqRel);
        }
        let mut flags = OpenFlags::from(self.flags.load(Ordering::Relaxed));
        flags.set(OpenFlags::O_CLOEXEC, close_on_exec);
        Ok(Arc::new(Self {
            buf: Arc::clone(&self.buf),
            write_end: self.write_end,
            flags: AtomicI32::new(flags.bits() | self.access_bits()),
        }))
    }

    fn stat(&self) -> FileAttr {
        FileAttr {
            // A pipe has no name, so no meaningful inode number, and only one
            // "link": the descriptor that names it.
            mode: InodeFileType::Fifo as mode_t | 0o600,
            nlinks: 1,
            ..FileAttr::default()
        }
    }

    fn flags(&self) -> OpenFlags {
        OpenFlags::from(self.flags.load(Ordering::Relaxed))
    }

    fn set_flags(&self, flags: OpenFlags) {
        self.flags
            .store(flags.bits() | self.access_bits(), Ordering::Relaxed);
    }

    fn poll(&self, events: u32) -> u32 {
        match self.write_end {
            true => {
                if self.buf.readers.load(Ordering::Acquire) == 0 {
                    // The reader is gone: the next `write()` is `EPIPE`, and
                    // there is no peer left to read what is queued.
                    POLLERR | POLLHUP
                } else if self.buf.data.lock().len() < PIPE_CAPACITY && events & POLLOUT != 0 {
                    POLLOUT
                } else {
                    0
                }
            }
            false => {
                let mut revents = 0;
                if !self.buf.data.lock().is_empty() && events & POLLIN != 0 {
                    revents |= POLLIN;
                }
                if self.buf.writers.load(Ordering::Acquire) == 0 {
                    // A `read()` would return 0 immediately, so `POLLIN` is
                    // ready even with an empty queue, and `POLLHUP` reports
                    // the closed peer.
                    revents |= POLLHUP;
                    if events & POLLIN != 0 {
                        revents |= POLLIN;
                    }
                }
                revents
            }
        }
    }
}

impl Drop for PipeEnd {
    fn drop(&mut self) {
        if self.write_end {
            self.buf.writers.fetch_sub(1, Ordering::AcqRel);
        } else {
            self.buf.readers.fetch_sub(1, Ordering::AcqRel);
        }
        // The peer may be blocked in `read()` (end of file) or `write()`
        // (`EPIPE`); both learn about it from the epoch.
        self.buf.bump();
    }
}

/// Create the two ends of one pipe.
///
/// `flags` carries the `O_NONBLOCK` / `O_CLOEXEC` bits the caller passed to
/// `pipe2()`; the returned handles already have them, so no post-creation
/// `fcntl` is needed (and none is possible, since the descriptors do not exist
/// yet when this runs).
pub fn create(flags: OpenFlags) -> (Arc<dyn FileOps>, Arc<dyn FileOps>) {
    let buf = Arc::new(PipeBuffer::new());
    let common = flags.bits();
    let read_end = Arc::new(PipeEnd {
        buf: Arc::clone(&buf),
        write_end: false,
        flags: AtomicI32::new(libc::O_RDONLY | common),
    }) as Arc<dyn FileOps>;
    let write_end = Arc::new(PipeEnd {
        buf,
        write_end: true,
        flags: AtomicI32::new(libc::O_WRONLY | common),
    }) as Arc<dyn FileOps>;
    (read_end, write_end)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn write_then_read_round_trips_bytes() {
        let (r, w) = create(OpenFlags::empty());
        assert_eq!(w.write(b"hello").unwrap(), 5);
        let mut buf = [0u8; 16];
        let n = r.read(&mut buf).unwrap();
        assert_eq!(&buf[..n], b"hello");
    }

    #[test]
    fn read_on_write_end_is_ebadf() {
        let (_r, w) = create(OpenFlags::empty());
        let mut buf = [0u8; 4];
        assert_eq!(w.read(&mut buf).unwrap_err(), code::EBADF);
    }

    #[test]
    fn empty_pipe_with_reader_closed_is_epipe() {
        let (r, w) = create(OpenFlags::empty());
        drop(r);
        assert_eq!(w.write(b"x").unwrap_err(), code::EPIPE);
    }

    #[test]
    fn drained_pipe_with_writer_closed_is_eof() {
        let (r, w) = create(OpenFlags::empty());
        drop(w);
        let mut buf = [0u8; 8];
        assert_eq!(r.read(&mut buf).unwrap(), 0);
    }

    #[test]
    fn nonblocking_read_on_empty_pipe_is_eagain() {
        let (r, _w) = create(OpenFlags::O_NONBLOCK);
        let mut buf = [0u8; 4];
        assert_eq!(r.read(&mut buf).unwrap_err(), code::EAGAIN);
    }

    #[test]
    fn eof_waits_for_every_write_end() {
        let (r, w) = create(OpenFlags::O_NONBLOCK);
        let w2 = w.dup(false).unwrap();
        drop(w);
        let mut buf = [0u8; 4];
        // A duplicate still holds the write end open, so the pipe is not at
        // end-of-file yet.
        assert_eq!(r.read(&mut buf).unwrap_err(), code::EAGAIN);
        drop(w2);
        assert_eq!(r.read(&mut buf).unwrap(), 0);
    }

    #[test]
    fn dup_shares_the_queue() {
        let (r, w) = create(OpenFlags::empty());
        let w2 = w.dup(false).unwrap();
        assert_eq!(w2.write(b"ab").unwrap(), 2);
        let mut buf = [0u8; 4];
        assert_eq!(r.read(&mut buf).unwrap(), 2);
        // Closing the original write end does not close the duplicate.
        drop(w);
        assert_eq!(w2.write(b"c").unwrap(), 1);
    }
}
