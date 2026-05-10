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

use core::arch::{asm, naked_asm};

/// Represents different DSB options for the AArch64 architecture
#[derive(Debug, Clone, Copy)]
pub enum DsbOptions {
    InnerShareable,
    OuterShareable,
    NonShareable,
    Sys,
}

#[inline]
pub fn wait_for_interrupt() {
    // SAFETY: This doesn't access memory in any way.
    unsafe {
        asm!("wfi", options(nomem, nostack));
    }
}

#[inline]
pub fn signal_event() {
    // SAFETY: This doesn't access memory in any way.
    unsafe {
        asm!("sev", options(nomem, nostack));
    }
}

#[inline]
pub fn wait_for_event() {
    // SAFETY: This doesn't access memory in any way.
    unsafe {
        asm!("wfe", options(nomem, nostack));
    }
}

#[inline]
pub fn isb() {
    // SAFETY: This doesn't access memory in any way.
    unsafe {
        asm!("isb", options(nostack, nomem, preserves_flags));
    }
}

#[inline]
pub fn isb_sy() {
    // SAFETY: This doesn't access memory in any way.
    unsafe {
        asm!("isb sy", options(nostack, nomem, preserves_flags));
    }
}

/// Execute a DSB instruction with the given option
pub fn dsb(option: DsbOptions) {
    // SAFETY: This doesn't access memory in any way.
    unsafe {
        match option {
            DsbOptions::InnerShareable => {
                asm!("dsb ish", options(nostack, nomem, preserves_flags))
            }
            DsbOptions::OuterShareable => {
                asm!("dsb osh", options(nostack, nomem, preserves_flags))
            }
            DsbOptions::NonShareable => {
                asm!("dsb nsh", options(nostack, nomem, preserves_flags))
            }
            DsbOptions::Sys => asm!("dsb sy", options(nostack, nomem, preserves_flags)),
        }
    }
}

// clear tlb
pub fn tlbi_all() {
    unsafe {
        asm!("tlbi vmalle1", options(nostack, preserves_flags));
    }
}
