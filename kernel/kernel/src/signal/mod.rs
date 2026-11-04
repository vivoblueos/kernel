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

use crate::{arch, scheduler, thread, thread::Thread};

pub mod delivery;
pub mod posix;

fn handle_signal_fallback(signum: i32) {
    if signum != libc::SIGTERM {
        return;
    }
    scheduler::retire_me();
}

fn handle_signal(t: &Thread, signum: i32) {
    let mut l = t.lock();
    let Some(handler) = l.take_signal_handler(signum) else {
        drop(l);
        return handle_signal_fallback(signum);
    };
    drop(l);
    handler();
}

pub(crate) fn handle_signals() {
    // Deliver the POSIX signals first: a program that installed a handler
    // expects it to run, and the kernel's own mechanism (a Rust closure
    // registered with `kill_with_once_handler`) is the fallback for the
    // signals POSIX does not cover.
    delivery::deliver_pending();

    let this = scheduler::current_thread_ref();
    let sigset = this.lock().pending_signals();
    // A signal the thread's POSIX mask holds back is *not* this mechanism's
    // to take: it has to stay pending until `sigprocmask()` unblocks it or a
    // `sigwait()` consumes it. Clearing it here would make the signal
    // disappear from `sigpending()` and from the wait that is expecting it.
    let blocked = this.signal_mask().blocked() as u32;
    // Signal `n` lives in bit `n`; signal 0 does not exist, so the scan starts
    // at 1 and stops below `NSIG`.
    for i in 1..posix::NSIG as i32 {
        if sigset & (1 << i) == 0 || blocked & (1 << i) != 0 {
            continue;
        }
        handle_signal(this, i);
        this.lock().clear_signal(i);
    }
}

// This routine is supposed to be executed in THREAD mode.
#[inline(never)]
pub(crate) unsafe extern "C" fn handler_entry(_sp: usize, _old_sp: usize) {
    let current = scheduler::current_thread();
    let sigset = current.lock().pending_signals();
    let blocked = current.signal_mask().blocked() as u32;
    for i in 1..posix::NSIG as i32 {
        if sigset & (1 << i) == 0 || blocked & (1 << i) != 0 {
            continue;
        }
        handle_signal(&current, i);
        current.lock().clear_signal(i);
    }
    {
        let mut l = current.lock();
        l.deactivate_signal_context();
    }
    let ok = current.transfer_state(thread::RUNNING, thread::READY);
    debug_assert_eq!(ok, Ok(()));
    let mut hook_holder = scheduler::ContextSwitchHookHolder::new(current);
    // We are switching from current thread's signal context to its thread
    // context.
    arch::switch_context_with_hook(&mut hook_holder as *mut _);
}
