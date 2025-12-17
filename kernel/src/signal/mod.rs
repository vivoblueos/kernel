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

use crate::{arch, scheduler, thread, thread::ThreadNode};

pub mod syscall;

fn handle_signal_fallback(signum: i32) {
    if signum != libc::SIGTERM {
        return;
    }
    scheduler::retire_me();
}

fn handle_signal(t: &ThreadNode, signum: i32) {
    // Don't use once handler now
    // POSIX-ish: consult installed sigaction.
    let sa = {
        let l = t.lock();
        l.get_sigaction(signum)
    };

    // None => SIG_DFL in our kernel representation.
    let Some(handler) = sa.sa_handler else {
        // almost all non realtime signals' default action is terminate the process
        return handle_signal_fallback(signum);
    };

    handler(signum);
}

// This routine is supposed to be executed in THREAD mode.
#[inline(never)]
pub(crate) unsafe extern "C" fn handler_entry(_sp: usize, _old_sp: usize) {
    let current = scheduler::current_thread();
    // Deliver only unblocked signals.
    // NOTE: pending_signals uses kernel numbering (bit = 1<<signum).
    // blocked uses POSIX numbering (bit = 1<<(signum-1)).
    let sigset = current.lock().pending_signals();
    for signum in 1..32 {
        if sigset & (1 << signum) == 0 {
            continue;
        }
        let blocked = current.lock().is_signal_blocked(signum);
        if blocked {
            continue;
        }

        handle_signal(&current, signum);
        // Clear the delivered signal from pending set.
        current.lock().clear_signal(signum);
    }
    {
        let mut l = current.lock();
        l.deactivate_signal_context();
        // after handling signals, the saved_sp should be restored to thread context,
        // add an assert here to make sure?
    }
    let saved_sp = current.saved_sp();
    current.transfer_state(thread::RUNNING, thread::READY);
    let mut hook_holder = scheduler::ContextSwitchHookHolder::new(current);
    // We are switching from current thread's signal context to its thread
    // context.
    arch::restore_context_with_hook(saved_sp, &mut hook_holder as *mut _);
}
