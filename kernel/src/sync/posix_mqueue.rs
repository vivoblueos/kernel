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

use crate::{
    error::Error,
    sync::{
        mqueue::{MessageQueue, SendMode},
        SpinLock,
    },
    syscall_handlers::mq_attr,
    time::{self, NO_WAITING, WAITING_FOREVER},
    types::Arc,
};
use alloc::{
    collections::BTreeMap,
    string::{String, ToString},
    vec::Vec,
};
use blueos_header::syscalls::NR::{MqGetSetAttr, MqOpen, MqTimedReceive, MqTimedSend, MqUnlink};
use core::{
    ffi::CStr,
    sync::atomic::{AtomicU32, Ordering},
};

use libc::{c_char, c_int, c_long, c_uint, mode_t, size_t, timespec};

const DEFAULT_MAXMSG: usize = 16;
const DEFAULT_MSGSIZE: usize = 128;

struct MQ {
    queue: Arc<MessageQueue>,
    flags: AtomicU32,
}

struct MQRegistry {
    next_fd: i32,
    fds: BTreeMap<i32, Arc<MQ>>,
    by_name: BTreeMap<String, Arc<MQ>>,
}

impl MQRegistry {
    const fn new() -> Self {
        Self {
            next_fd: 256, // start mq fd range away from file descriptors
            fds: BTreeMap::new(),
            by_name: BTreeMap::new(),
        }
    }

    fn alloc_fd(&mut self) -> i32 {
        let fd = self.next_fd;
        self.next_fd += 1;
        fd
    }
}

static REG: SpinLock<MQRegistry> = SpinLock::new(MQRegistry::new());

fn get_mq(fd: c_int) -> Option<Arc<MQ>> {
    let reg = REG.lock();
    reg.fds.get(&fd).cloned()
}

fn to_ticks(timeout: *const timespec) -> Option<usize> {
    if timeout.is_null() {
        return None;
    }
    let ts = unsafe { &*timeout };
    let ms = ts.tv_sec * 1000 + ts.tv_nsec / 1_000_000;
    if ms < 0 {
        return Some(0);
    }
    Some(time::tick_from_millisecond(ms as usize))
}

fn err(e: Error) -> c_int {
    -(e.to_errno() as c_int)
}

pub fn mq_open(name: *const c_char, oflag: c_int, _mode: mode_t, attr: *const mq_attr) -> c_int {
    if name.is_null() {
        return -libc::EINVAL;
    }
    let cstr = unsafe { CStr::from_ptr(name) };
    let raw_name = match cstr.to_str() {
        Ok(s) => s,
        Err(_) => return -libc::EINVAL,
    };
    if raw_name.is_empty() {
        return -libc::EINVAL;
    }
    let raw_name = raw_name.to_string();
    let create = (oflag & libc::O_CREAT) != 0;
    let excl = (oflag & libc::O_EXCL) != 0;
    let nonblock = (oflag & libc::O_NONBLOCK) != 0;

    let mut reg: crate::sync::SpinLockGuard<'_, MQRegistry> = REG.lock();

    if let Some(existing) = reg.by_name.get(&raw_name).cloned() {
        if create && excl {
            return -libc::EEXIST;
        }
        let fd = reg.alloc_fd();
        reg.fds.insert(fd, existing);
        return fd;
    }

    if !create {
        return -libc::ENOENT;
    }

    // Build attributes
    let (maxmsg, msgsize) = if attr.is_null() {
        (DEFAULT_MAXMSG as u32, DEFAULT_MSGSIZE as usize)
    } else {
        let a = unsafe { &*attr };
        if a.mq_maxmsg <= 0 || a.mq_msgsize <= 0 {
            return -libc::EINVAL;
        }
        (a.mq_maxmsg as u32, a.mq_msgsize as usize)
    };

    let q = Arc::new(MessageQueue::new(msgsize, maxmsg, core::ptr::null_mut()));
    if !q.init() {
        return -libc::EFAULT;
    }

    let mq = Arc::new(MQ {
        queue: q,
        flags: AtomicU32::new(if nonblock { libc::O_NONBLOCK as u32 } else { 0 }),
    });

    reg.by_name.insert(raw_name, mq.clone());
    let fd = reg.alloc_fd();
    reg.fds.insert(fd, mq);

    fd
}

pub fn mq_close(fd: c_int) -> c_int {
    let mut reg = REG.lock();
    if reg.fds.remove(&fd).is_some() {
        0
    } else {
        -libc::EBADF
    }
}

pub fn mq_unlink(name: *const c_char) -> c_int {
    if name.is_null() {
        return -libc::EINVAL;
    }
    let cstr = unsafe { CStr::from_ptr(name) };
    let raw_name = match cstr.to_str() {
        Ok(s) => s,
        Err(_) => return -libc::EINVAL,
    };
    // already canonicalized in posix interface
    let key = raw_name.to_string();
    let mut reg = REG.lock();
    if reg.by_name.remove(&key).is_some() {
        0
    } else {
        -libc::ENOENT
    }
}

pub fn mq_timedsend(
    fd: c_int,
    msg_ptr: *const c_char,
    msg_len: size_t,
    msg_prio: c_uint,
    timeout: *const timespec,
) -> c_int {
    if msg_ptr.is_null() || msg_len == 0 {
        return -libc::EINVAL;
    }
    let mq = match get_mq(fd) {
        Some(m) => m,
        None => return -libc::EBADF,
    };
    let timed = !timeout.is_null();
    let is_nonblock = (mq.flags.load(Ordering::Relaxed) & (libc::O_NONBLOCK as u32)) != 0;
    let timeout = if timed {
        to_ticks(timeout).unwrap_or(WAITING_FOREVER)
    } else if is_nonblock {
        NO_WAITING
    } else {
        WAITING_FOREVER
    };

    let slice = unsafe { core::slice::from_raw_parts(msg_ptr as *const u8, msg_len) };
    let mode = if msg_prio > 0 {
        SendMode::Urgent
    } else {
        SendMode::Normal
    };
    match mq.queue.send(slice, msg_len, timeout, mode) {
        Ok(()) => 0,
        Err(e) => {
            if e.to_errno() == libc::ETIMEDOUT && is_nonblock && !timed {
                -libc::EAGAIN
            } else {
                err(e)
            }
        }
    }
}

pub fn mq_timedrecv(
    fd: c_int,
    msg_ptr: *mut c_char,
    msg_len: size_t,
    msg_prio: *mut c_uint,
    timeout: *const timespec,
) -> c_int {
    if msg_ptr.is_null() || msg_len == 0 {
        return -libc::EINVAL;
    }
    let mq = match get_mq(fd) {
        Some(m) => m,
        None => return -libc::EBADF,
    };
    let timed = !timeout.is_null();
    let is_nonblock = (mq.flags.load(Ordering::Relaxed) & (libc::O_NONBLOCK as u32)) != 0;
    let timeout = if timed {
        to_ticks(timeout).unwrap_or(WAITING_FOREVER)
    } else if is_nonblock {
        NO_WAITING
    } else {
        WAITING_FOREVER
    };

    let buf = unsafe { core::slice::from_raw_parts_mut(msg_ptr as *mut u8, msg_len) };
    match mq.queue.recv(buf, msg_len, timeout) {
        Ok(()) => {
            if !msg_prio.is_null() {
                unsafe { *msg_prio = 0 };
            }
            msg_len as c_int
        }
        Err(e) => {
            if e.to_errno() == libc::ETIMEDOUT && is_nonblock && !timed {
                -libc::EAGAIN
            } else {
                err(e)
            }
        }
    }
}

pub fn mq_getsetattr(fd: c_int, new: *const mq_attr, old: *mut mq_attr) -> c_int {
    let mq = match get_mq(fd) {
        Some(m) => m,
        None => return -libc::EBADF,
    };
    if !old.is_null() {
        let (node_size, node_cnt) = mq.queue.node_info();
        let curmsgs = mq.queue.recvable_count() as c_long;
        unsafe {
            (*old).mq_flags = mq.flags.load(Ordering::Relaxed) as c_long;
            (*old).mq_maxmsg = node_cnt as c_long;
            (*old).mq_msgsize = (node_size - core::mem::size_of::<usize>()) as c_long;
            (*old).mq_curmsgs = curmsgs;
        }
    }
    if !new.is_null() {
        let n = unsafe { &*new };
        // Only O_NONBLOCK supported
        let new_flags = (n.mq_flags as u32) & (libc::O_NONBLOCK as u32);
        mq.flags.store(new_flags, Ordering::Relaxed);
    }
    0
}
