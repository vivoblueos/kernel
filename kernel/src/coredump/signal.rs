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

//! Fault-type to signal number mapping.
//!
//! Each architecture provides a function that maps its fault exception
//! class/code to a POSIX signal number (from libc).

// libc signal numbers
const SIGILL: i32 = 4;
const SIGTRAP: i32 = 5;
const SIGABRT: i32 = 6;
const SIGFPE: i32 = 8;
const SIGBUS: i32 = 10;
const SIGSEGV: i32 = 11;

/// Map AArch64 ESR Exception Class (EC) to a signal number.
pub fn aarch64_ec_to_signo(ec: u64) -> i32 {
    match ec {
        // Instruction abort (MMU)
        0x20 | 0x21 => SIGSEGV,
        // Data abort (MMU)
        0x24 | 0x25 => SIGSEGV,
        // SP alignment fault
        0x26 => SIGBUS,
        // SError
        0x2F => SIGBUS,
        // Breakpoint, watchpoint, etc.
        0x30..=0x35 => SIGTRAP,
        // Unknown EC
        0x00 => SIGILL,
        // Everything else
        _ => SIGILL,
    }
}

/// Map RISC-V mcause exception code to a signal number.
///
/// `mcause` exception codes (interrupt bit masked out already):
///   0: instruction address misaligned
///   1: instruction access fault
///   2: illegal instruction
///   3: breakpoint
///   4: load address misaligned
///   5: load access fault
///   6: store address misaligned
///   7: store access fault
///   8: ecall from U-mode
///   9: ecall from S-mode
///  10: reserved
///  11: ecall from M-mode
///  12: instruction page fault
///  13: load page fault
///  14: reserved
///  15: store page fault
pub fn riscv_mcause_to_signo(mcause: usize) -> i32 {
    match mcause {
        1..=3 => SIGBUS,
        4 => SIGSEGV,
        5 => SIGSEGV,
        6 => SIGILL,
        8 => SIGILL,
        12 => SIGSEGV,
        13 => SIGSEGV,
        15 => SIGSEGV,
        _ => SIGILL,
    }
}

/// Map ARM Cortex-M CFSR fault type to a signal number.
///
/// CFSR is a 32-bit register formed from:
///   [31:16] MMFSR (MemManage Fault Status)
///   [15:8]  BFSR  (Bus Fault Status)
///   [7:0]   UFSR  (Usage Fault Status)
pub fn arm_cfsr_to_signo(cfsr: u32) -> i32 {
    // Usage Fault status (low 8 bits)
    let ufsr = (cfsr & 0xFF) as u8;
    // Bus Fault status (bits 15:8)
    let bfsr = ((cfsr >> 8) & 0xFF) as u8;
    // MemManage Fault status (bits 31:16)
    let mmfsr = ((cfsr >> 16) & 0xFF) as u8;

    // Memory management faults take precedence
    if arm_mmfsr_has_fault(mmfsr) {
        // IACCVIOL (instruction access) → SIGSEGV
        // DACCVIOL (data access) → SIGSEGV
        return SIGSEGV;
    }

    // Bus faults
    if arm_bfsr_has_fault(bfsr) {
        // IBUSERR, PRECISERR, IMPRECISERR, UNSTKERR, STKERR → SIGBUS
        return SIGBUS;
    }

    // Usage faults
    if ufsr & 0x01 != 0 {
        // UNDEFINSTR → SIGILL
        return SIGILL;
    }
    if ufsr & 0x02 != 0 {
        // INVSTATE → SIGILL
        return SIGILL;
    }
    if ufsr & 0x04 != 0 {
        // INVPC → SIGILL
        return SIGILL;
    }
    if ufsr & 0x08 != 0 {
        // NOCP → SIGILL
        return SIGILL;
    }
    if ufsr & 0x10 != 0 {
        // UNALIGNED → SIGBUS
        return SIGBUS;
    }
    if ufsr & 0x20 != 0 {
        // DIVBYZERO → SIGFPE
        return SIGFPE;
    }

    SIGILL
}

fn arm_mmfsr_has_fault(mmfsr: u8) -> bool {
    // Bits: IACCVIOL(0), DACCVIOL(1), MLSPERR(2), MSTKERR(3), MUNSTKERR(4)
    mmfsr & 0x1F != 0
}

fn arm_bfsr_has_fault(bfsr: u8) -> bool {
    // Bits: IBUSERR(0), PRECISERR(1), IMPRECISERR(2), UNSTKERR(3), STKERR(4)
    bfsr & 0x1F != 0
}

/// Signal number for a generic kernel panic.
pub fn panic_signo() -> i32 {
    SIGABRT
}