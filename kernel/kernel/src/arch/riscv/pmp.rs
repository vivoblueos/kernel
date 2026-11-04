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

//! Physical memory protection, sized for the one thing the kernel needs today:
//! letting U-mode touch memory at all.
//!
//! # Why this is not optional
//!
//! RISC-V checks PMP **before** translation, and the spec is blunt about the
//! no-match case: an S-mode or U-mode access that matches no PMP entry **fails**,
//! while an M-mode access that matches no entry succeeds. A kernel that never
//! programs PMP therefore behaves exactly like a machine where U-mode has no
//! memory at all: the first instruction fetch of the first user image raises
//! `mcause = 1` (instruction access fault) with `mepc`/`mtval` at the image's
//! entry point — the symptom that took a debug session to trace back here,
//! because everything else (satp mode, PTE flags, translation walk) was already
//! correct.
//!
//! # What the current policy is
//!
//! One NAPOT entry covering the low 4 GiB, `R | W | X`, `L = 0`:
//!
//! - `L = 0` keeps M-mode unrestricted. Per the spec, an M-mode access is only
//!   permission-checked against an entry when that entry is locked, so the
//!   kernel keeps its full run of the machine.
//! - The 4 GiB hole covers QEMU `virt` RAM (0x8000_0000) and the image base
//!   (0x0001_0000), so user images are reachable without teaching early boot
//!   the platform's memory map.
//!
//! This is deliberately coarse. U-mode's *virtual* reach is already fenced in
//! by the per-process page table, which maps only the image's own segments;
//! PMP is the physical backstop that makes the access legal in the first place.
//! Tightening it to the real RAM window belongs to the board layer, which is the
//! only place that knows where RAM ends.

/// Byte 0 of `pmpcfg0`: entry 0's flags, `R | W | X | A = NAPOT (3)`, `L = 0`.
///
/// `L` must stay clear: a locked entry would also gate M-mode against these
/// permissions, and a locked entry can never be unlocked again before reset.
const CFG_RWX_NAPOT: usize = 0b0001_1111;

/// `pmpaddr0` for a NAPOT region of `2^32` bytes starting at 0.
///
/// NAPOT encodes base and size in one register: the number of trailing ones
/// `k` in `pmpaddr` gives a size of `2^(k + 3)`, and the address is everything
/// above those ones, shifted left by 2. `size = 2^32` needs `k = 29` trailing
/// ones, i.e. `2^29 - 1` with zero high bits — base 0, size 4 GiB.
const PMPADDR0_NAPOT_4GIB: usize = (1 << 29) - 1;

const _: () = assert!(PMPADDR0_NAPOT_4GIB == 0x1fff_ffff);

/// Open the low 4 GiB to U-mode. Must run on **every** hart.
///
/// `pmpcfg0`/`pmpaddr0` are per-hart CSRs with no inheritance: a hart that skips
/// this call faults on the first user access it ever makes, which on an SMP
/// machine surfaces as a crash that depends on which hart the scheduler
/// happened to run the thread on.
///
/// The address is written before the config byte so the hart never sees a
/// configured entry whose address is still whatever reset left there.
///
/// # Safety
///
/// Writes machine CSRs; call once per hart during early boot, before any thread
/// can enter U-mode.
#[cfg(target_pointer_width = "64")]
pub(crate) unsafe fn open_user_window() {
    core::arch::asm!(
        "csrw pmpaddr0, {addr}",
        "csrw pmpcfg0, {cfg}",
        addr = in(reg) PMPADDR0_NAPOT_4GIB,
        cfg = in(reg) CFG_RWX_NAPOT,
        options(nostack),
    );
}

/// 32-bit boards have no MMU and no user processes (`mmu` is compiled out), so
/// there is nothing to protect and nothing that would observe the entry.
#[cfg(not(target_pointer_width = "64"))]
pub(crate) unsafe fn open_user_window() {}
