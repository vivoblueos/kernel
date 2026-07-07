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

// ---------------------------------------------------------------------------
// TLBI observation hook (test-only, Phase 5a task 3.5)
// ---------------------------------------------------------------------------
// `#[cfg(test)]` counters incremented on every `tlbi_aside1is` /
// `tlbi_vmalle1is` call, so scheduler context-switch tests (§7) can verify
// that a TLB invalidation was actually issued rather than asserting it by
// hand-wave.  Compiled out of production builds.
//
// Implemented as `static mut u64` (plain load/store) rather than `AtomicU64`:
// an atomic RMW (exclusive-monitor access) on this `.bss` static previously
// faulted under the hot 256-call `alloc` loop in `test_asid_recycle_does_not_panic`
// (EL1 Data Abort, EC 0x25).  The unittest harness accesses these counters
// single-threaded (reset → exercise → read), so non-atomic access is safe.
// `static_mut_refs` is allow-listed by the build (`-A static_mut_refs`).
#[cfg(test)]
static mut TLBI_ASIDE1IS_COUNT: u64 = 0;
#[cfg(test)]
static mut TLBI_VMALLE1IS_COUNT: u64 = 0;

/// Reset both TLBI spy counters (call at the start of a test that checks
/// issuance).  Test-only.
#[cfg(test)]
pub(crate) fn reset_tlbi_counters() {
    // SAFETY: test-only, single-threaded access (unittest harness).
    unsafe {
        TLBI_ASIDE1IS_COUNT = 0;
        TLBI_VMALLE1IS_COUNT = 0;
    }
}

/// Read both TLBI spy counters as `(aside1is_count, vmalle1is_count)`.
/// Test-only.
#[cfg(test)]
pub(crate) fn read_tlbi_counters() -> (u64, u64) {
    // SAFETY: test-only, single-threaded access (unittest harness).
    unsafe { (TLBI_ASIDE1IS_COUNT, TLBI_VMALLE1IS_COUNT) }
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

/// Invalidate the entire TLB (TLBI VMALLE1), Inner Shareable.
///
/// Unlike [`tlbi_all`] which is `tlbi vmalle1` (local PE only), this broadcasts
/// the invalidation to all CPUs in the Inner Shareable domain.  Used when
/// switching to a kernel thread: the retiring user process's ASID+PA must be
/// purged from every CPU's TLB, not just the current one.  See design D2.
#[inline]
pub fn tlbi_vmalle1is() {
    #[cfg(test)]
    unsafe {
        TLBI_VMALLE1IS_COUNT += 1;
    }
    unsafe {
        asm!("tlbi vmalle1is", options(nostack, preserves_flags));
    }
}

/// Invalidate TLB entries by ASID, Inner Shareable (TLBI ASIDE1IS).
/// `asid` occupies bits [63:48] of the operand register.
#[inline]
pub fn tlbi_aside1is(asid: u8) {
    #[cfg(test)]
    unsafe {
        TLBI_ASIDE1IS_COUNT += 1;
    }
    let val: u64 = (asid as u64) << 48;
    unsafe {
        asm!("tlbi aside1is, {x}", x = in(reg) val, options(nostack, preserves_flags));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    // W4: Smoke test — tlbi_aside1is must execute without panicking for a
    // representative ASID value.  Runs at EL1 under QEMU; the instruction is
    // a no-op semantically for the test (no TLB entries to invalidate) but
    // proves the encoding/asm wrapper is well-formed.
    #[test]
    fn test_tlbi_aside1is_does_not_panic() {
        tlbi_aside1is(1);
        tlbi_aside1is(255);
        tlbi_aside1is(0);
    }

    // Phase 5a task 1.1: Smoke test — tlbi_vmalle1is (Inner-Shareable full
    // TLB invalidation) must execute without panicking.  Used by the
    // scheduler's kernel-thread switch path (design D2).
    #[test]
    fn test_tlbi_vmalle1is_does_not_panic() {
        tlbi_vmalle1is();
    }

    // Phase 5a task 3.5: The TLBI spy counters must increment on each call
    // and reset cleanly.  This is the harness the §7 scheduler tests rely on
    // to observe TLBI issuance.
    #[test]
    fn test_tlbi_spy_counters_increment_and_reset() {
        reset_tlbi_counters();
        assert_eq!(read_tlbi_counters(), (0, 0), "counters must start at 0 after reset");
        tlbi_aside1is(7);
        tlbi_aside1is(8);
        tlbi_vmalle1is();
        let (aside, vmall) = read_tlbi_counters();
        assert_eq!(aside, 2, "aside1is counter must record 2 calls");
        assert_eq!(vmall, 1, "vmalle1is counter must record 1 call");
        reset_tlbi_counters();
        assert_eq!(read_tlbi_counters(), (0, 0), "reset must zero both counters");
    }
}
