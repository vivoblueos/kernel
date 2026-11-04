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

//! POSIX `poll()` / `ppoll()` support: event bits and the C `struct pollfd`.
//!
//! The event bits follow the values newlib's `<poll.h>` shim declares (see
//! `external/quickjs-ng/bk_include/poll.h`), because the C caller and the
//! kernel have to agree on the exact bit positions.

use crate::thread::POLL_EPOCH;
use crate::time::Tick;
use crate::vfs::uptr;
use alloc::vec::Vec;
use blueos_infra::no_let_underscore::IgnoreResult;
use core::ffi::{c_int, c_long, c_short, c_ulong};
use libc::sigset_t;

/// Re-exported so a caller that already knows about [`crate::vfs::poll`] can
/// bump the epoch without also having to know where it is stored. The storage
/// lives in [`crate::thread`] because the signal path has to reach it and
/// cannot depend on the VFS, which some targets leave out.
pub use crate::thread::{bump_poll_epoch, poll_epoch};

/// The most descriptors one `poll()` call may name.
///
/// POSIX only requires `OPEN_MAX`; the cap keeps a single call from walking
/// an unbounded user array.
pub const POLL_NFDS_MAX: usize = 1024;

/// Data other than high-priority data may be read without blocking.
pub const POLLIN: u32 = 0x0001;
/// High-priority data may be read without blocking.
pub const POLLPRI: u32 = 0x0002;
/// Normal data may be written without blocking.
pub const POLLOUT: u32 = 0x0004;
/// An error has occurred on the device or stream.
pub const POLLERR: u32 = 0x0008;
/// The device has been disconnected, or the peer closed its end.
pub const POLLHUP: u32 = 0x0010;
/// The `fd` is not an open file.
pub const POLLNVAL: u32 = 0x0020;

/// Normal data may be read without blocking (alias of [`POLLIN`] here).
pub const POLLRDNORM: u32 = 0x0040;
/// Normal data may be written without blocking (alias of [`POLLOUT`]).
pub const POLLWRNORM: u32 = 0x0100;

/// Every bit a caller may set in `events`, or see in `revents`.
pub const POLL_ALL: u32 = POLLIN | POLLPRI | POLLOUT | POLLERR | POLLHUP | POLLNVAL;

/// The C `struct pollfd` as newlib lays it out.
///
/// ```text
/// struct pollfd {
///     int   fd;        // offset 0, 4 bytes
///     short events;    // offset 4, 2 bytes
///     short revents;   // offset 6, 2 bytes
/// };                   // size 8
/// ```
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub struct PollFd {
    pub fd: c_int,
    pub events: c_short,
    pub revents: c_short,
}

/// Reports the events one descriptor is ready for, or [`POLLNVAL`] if it is
/// not open.
///
/// The fd table lock is dropped before the query runs: for a socket the
/// query is answered by the network thread, which blocks, and an irqsave
/// lock must not be held across a wait.
fn ready_for(fd: c_int, requested: u32) -> u32 {
    use crate::vfs::syscalls::current_fd;

    let ops = {
        current_fd!(fd_manager, err: POLLNVAL);
        fd_manager.get_file_ops(fd)
    };
    match ops {
        Some(file) => file.poll(requested),
        None => POLLNVAL,
    }
}

/// Walks the `pollfd` array once and writes each entry's `revents`.
///
/// Returns how many entries ended up with a non-zero `revents`. A negative
/// `fd` is skipped and gets `revents` 0, as POSIX requires; a descriptor
/// that is not open gets [`POLLNVAL`].
fn scan(fds: *mut PollFd, nfds: usize) -> usize {
    let mut ready = 0;
    for i in 0..nfds {
        // SAFETY: the caller validated `fds`/`nfds` in `poll_impl`, so every
        // element of the array is inside readable, writable memory.
        let entry = unsafe { &mut *fds.add(i) };
        if entry.fd < 0 {
            entry.revents = 0;
            continue;
        }
        let requested = entry.events as u32 & POLL_ALL;
        let revents = ready_for(entry.fd, requested);
        entry.revents = revents as c_short;
        if revents != 0 {
            ready += 1;
        }
    }
    ready
}

/// The shared body of `poll()` and `ppoll()`.
///
/// `deadline` is an absolute tick, or `None` to wait forever. `sigmask`, when
/// given, replaces the thread's signal mask for the duration of the wait, so
/// that a signal arriving during the wait interrupts the call instead of
/// being delivered to a handler that runs after it returns.
fn poll_impl(
    fds: *mut PollFd,
    nfds: usize,
    deadline: Option<Tick>,
    sigmask: *const sigset_t,
) -> c_long {
    if nfds > POLL_NFDS_MAX {
        return -libc::EINVAL as c_long;
    }
    if nfds != 0 && fds.is_null() {
        return -libc::EINVAL as c_long;
    }

    let thread = crate::scheduler::current_thread();
    // `ppoll()` swaps the mask in for the wait and puts the old one back
    // afterwards. `poll()` leaves the mask alone.
    let mut saved_mask: Option<usize> = None;
    if !sigmask.is_null() {
        // SAFETY: `sigmask` points at a C `sigset_t`, which the kernel reads
        // as a pointer-width word (see `signal::posix::read_c_mask`).
        let requested = unsafe { *(sigmask as *const usize) };
        let mask = thread.signal_mask();
        saved_mask = Some(mask.blocked());
        mask.set_blocked(requested);
    }

    // A signal that is caught during the wait interrupts it with EINTR. Two
    // things have to be watched, because a signal only passes through one of
    // them: the pending set, if the signal has arrived but its disposition
    // has not been applied yet, and the delivery counter, if it already has.
    // The scheduler runs the disposition on the way back from a sleep, so
    // the second case is the common one - by the time this loop is scheduled
    // again the handler has run and the pending bit is clear.
    let mut delivered_at_entry = thread.signals_delivered();

    let result = loop {
        let epoch = poll_epoch();
        let ready = scan(fds, nfds);
        if ready != 0 {
            break ready as c_long;
        }

        // A handler ran while we were asleep: that is the EINTR case.
        let delivered = thread.signals_delivered();
        if delivered != delivered_at_entry {
            break -libc::EINTR as c_long;
        }
        delivered_at_entry = delivered;

        // A signal that is not blocked by the mask in force interrupts the
        // wait. Deliver it before returning so the handler runs first, as
        // POSIX requires.
        let blocked = thread.signal_mask().blocked();
        if thread.pending_signals() as usize & !blocked != 0 {
            crate::signal::delivery::deliver_pending();
            break -libc::EINTR as c_long;
        }

        if let Some(deadline) = deadline {
            let now = Tick::now();
            if now.0 >= deadline.0 {
                break 0;
            }
            // Wait only while the epoch is unchanged: anything that bumped it
            // after the scan above would otherwise be slept through. The wait
            // itself ends at the deadline, so a quiet system still times out.
            let remaining = Tick(deadline.0 - now.0);
            crate::sync::atomic_wait::atomic_wait(&POLL_EPOCH, epoch, remaining)
                .ignore_result();
        } else {
            crate::sync::atomic_wait::atomic_wait(&POLL_EPOCH, epoch, Tick::MAX).ignore_result();
        }
    };

    if let Some(old) = saved_mask {
        thread.signal_mask().set_blocked(old);
        // A signal that was held out for the duration of `ppoll()` is now
        // unblocked again; deliver it rather than leaving it pending until
        // the next unrelated scheduling point.
        crate::signal::delivery::deliver_pending();
    }

    result
}

/// POSIX `poll()`.
///
/// `fds` points at an array of [`PollFd`] (`struct pollfd`) and `nfds` gives
/// its length. `timeout_ms` is in milliseconds; a negative value means wait
/// forever and zero means return after the scan even if nothing is ready.
pub fn poll(fds: *mut core::ffi::c_void, nfds: usize, timeout_ms: c_int) -> c_long {
    let deadline = if timeout_ms < 0 {
        None
    } else {
        Some(Tick::after(Tick::from_millis(timeout_ms as u64)))
    };
    poll_impl(fds as *mut PollFd, nfds, deadline, core::ptr::null())
}

/// POSIX `ppoll()`.
///
/// The timeout is a `struct timespec` interval, relative to now - the same
/// quantity `poll()` takes in milliseconds. A null `timeout` waits forever;
/// a negative one is an error, unlike `poll()` where it means "forever".
/// `sigmask`, when non-null, replaces the thread's signal mask for the
/// duration of the wait.
pub fn ppoll(
    fds: *mut core::ffi::c_void,
    nfds: usize,
    timeout: *const libc::timespec,
    sigmask: *const sigset_t,
) -> c_long {
    let deadline = if timeout.is_null() {
        None
    } else {
        // SAFETY: `timeout` is non-null and the caller guarantees it points
        // at a readable `struct timespec`.
        let ts = unsafe { &*timeout };
        if ts.tv_sec < 0 || ts.tv_nsec < 0 || ts.tv_nsec >= 1_000_000_000 {
            return -libc::EINVAL as c_long;
        }
        let millis = ts.tv_sec as u64 * 1000 + (ts.tv_nsec as u64) / 1_000_000;
        Some(Tick::after(Tick::from_millis(millis)))
    };
    poll_impl(fds as *mut PollFd, nfds, deadline, sigmask)
}

/// `FD_SETSIZE` as newlib's `<sys/select.h>` declares it.
///
/// newlib keeps the historical value 64 (unlike glibc's 1024), and defines
/// `fd_set` as `unsigned long fds_bits[FD_SETSIZE / (8 * sizeof(long))]`.
/// The kernel has to agree with the C caller on that layout, so this is
/// spelled out rather than taken from `libc`, whose `fd_set` is the 1024-bit
/// glibc shape.
pub const FD_SETSIZE: usize = 64;

const FD_SET_BITS: usize = core::mem::size_of::<c_ulong>() * 8;
const FD_SET_WORDS: usize = FD_SETSIZE / FD_SET_BITS;

/// The C `fd_set` as newlib lays it out.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub struct FdSet {
    bits: [c_ulong; FD_SET_WORDS],
}

impl FdSet {
    fn contains(&self, fd: usize) -> bool {
        self.bits[fd / FD_SET_BITS] & ((1 as c_ulong) << (fd % FD_SET_BITS)) != 0
    }

    fn insert(&mut self, fd: usize) {
        self.bits[fd / FD_SET_BITS] |= (1 as c_ulong) << (fd % FD_SET_BITS);
    }
}

/// Read one `fd_set` argument, or `None` when the caller passed NULL.
fn read_fdset(ptr: *mut core::ffi::c_void) -> Result<Option<FdSet>, crate::error::Error> {
    if ptr.is_null() {
        return Ok(None);
    }
    uptr::read_struct::<FdSet>(ptr as *const FdSet).map(Some)
}

/// POSIX `select()`.
///
/// `nfds` is the highest descriptor plus one and may not exceed
/// [`FD_SETSIZE`]. The three sets are optional; a NULL set is ignored. `timeout`
/// is a `struct timeval` interval, or NULL to wait forever. The sets are
/// rewritten in place with the descriptors that are ready, and the return
/// value is how many descriptors appear in any of the output sets; a
/// descriptor that is not open gives `EBADF`.
pub fn select(
    nfds: c_int,
    readfds: *mut core::ffi::c_void,
    writefds: *mut core::ffi::c_void,
    exceptfds: *mut core::ffi::c_void,
    timeout: *mut libc::timeval,
) -> c_int {
    if nfds < 0 || nfds as usize > FD_SETSIZE {
        return -libc::EINVAL;
    }

    let read_set = match read_fdset(readfds) {
        Ok(set) => set,
        Err(err) => return err.to_errno(),
    };
    let write_set = match read_fdset(writefds) {
        Ok(set) => set,
        Err(err) => return err.to_errno(),
    };
    let except_set = match read_fdset(exceptfds) {
        Ok(set) => set,
        Err(err) => return err.to_errno(),
    };

    let deadline = if timeout.is_null() {
        None
    } else {
        let tv = match uptr::read_struct::<libc::timeval>(timeout) {
            Ok(tv) => tv,
            Err(err) => return err.to_errno(),
        };
        if tv.tv_sec < 0 || tv.tv_usec < 0 || tv.tv_usec >= 1_000_000 {
            return -libc::EINVAL;
        }
        let millis = tv.tv_sec as u64 * 1000 + (tv.tv_usec as u64) / 1000;
        Some(Tick::after(Tick::from_millis(millis)))
    };

    // One `pollfd` per descriptor below `nfds`; descriptors that no set
    // mentions get `fd = -1`, which `scan` skips without treating them as
    // `POLLNVAL`.
    let mut pfds: Vec<PollFd> = (0..nfds as usize)
        .map(|fd| {
            let mut events = 0u32;
            if read_set.as_ref().is_some_and(|set| set.contains(fd)) {
                events |= POLLIN;
            }
            if write_set.as_ref().is_some_and(|set| set.contains(fd)) {
                events |= POLLOUT;
            }
            if except_set.as_ref().is_some_and(|set| set.contains(fd)) {
                events |= POLLPRI;
            }
            PollFd {
                fd: if events == 0 { -1 } else { fd as c_int },
                events: events as c_short,
                revents: 0,
            }
        })
        .collect();

    let ret = poll_impl(pfds.as_mut_ptr(), pfds.len(), deadline, core::ptr::null());
    if ret < 0 {
        return ret as c_int;
    }

    // Unlike `poll()`, whose `POLLNVAL` is a per-entry event, `select()`
    // reports an unopened descriptor as an error for the whole call.
    if pfds
        .iter()
        .any(|entry| entry.revents as u32 & POLLNVAL != 0)
    {
        return -libc::EBADF;
    }

    let mut out_read = FdSet::default();
    let mut out_write = FdSet::default();
    let mut out_except = FdSet::default();
    let mut ready = 0;
    for (fd, entry) in pfds.iter().enumerate() {
        let revents = entry.revents as u32;
        let mut hit = false;
        // Err/hang-up make the descriptor readable and writable at once,
        // matching how Linux folds them into `select()`'s result sets.
        if read_set.is_some() && revents & (POLLIN | POLLERR | POLLHUP) != 0 {
            out_read.insert(fd);
            hit = true;
        }
        if write_set.is_some() && revents & (POLLOUT | POLLERR) != 0 {
            out_write.insert(fd);
            hit = true;
        }
        if except_set.is_some() && revents & POLLPRI != 0 {
            out_except.insert(fd);
            hit = true;
        }
        if hit {
            ready += 1;
        }
    }

    if read_set.is_some() {
        if let Err(err) = uptr::write_struct(readfds as *mut FdSet, &out_read) {
            return err.to_errno();
        }
    }
    if write_set.is_some() {
        if let Err(err) = uptr::write_struct(writefds as *mut FdSet, &out_write) {
            return err.to_errno();
        }
    }
    if except_set.is_some() {
        if let Err(err) = uptr::write_struct(exceptfds as *mut FdSet, &out_except) {
            return err.to_errno();
        }
    }

    ready
}
