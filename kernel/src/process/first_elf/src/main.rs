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

//! First user-space process (Phase 3 test ELF).
//!
//! This is a minimal no_std PIE binary that:
//! 1. Writes "Hello from EL0!\n" via SVC (syscall write to stdout)
//! 2. Calls exit_thread to terminate
//!
//! It is compiled as a static PIE (ET_DYN) for AArch64 and embedded into
//! the kernel image via `include_bytes!` for the first process test.

#![no_std]
#![no_main]

// ---------------------------------------------------------------------------
// Syscall numbers (must match kernel/header/src/lib.rs)
// ---------------------------------------------------------------------------

const NR_WRITE: usize = 11;
const NR_EXIT_THREAD: usize = 6;

// File descriptor for stdout.
const STDOUT: usize = 1;

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/// The _start entry expected by the ELF loader.
///
/// The AArch64 SVC calling convention places:
/// - NR in x8
/// - args in x0 - x5
#[no_mangle]
pub extern "C" fn _start() -> ! {
    let msg = b"Hello from EL0!\n";
    let ret = syscall_write(STDOUT, msg.as_ptr() as usize, msg.len());
    syscall_exit_thread(ret as usize);
    loop {}
}

// ---------------------------------------------------------------------------
// Syscall wrappers
// ---------------------------------------------------------------------------

/// Write syscall: write(fd, buf, count)
fn syscall_write(fd: usize, buf: usize, count: usize) -> isize {
    let ret: isize;
    unsafe {
        core::arch::asm!(
            "svc #0",
            in("x8") NR_WRITE,
            in("x0") fd,
            in("x1") buf,
            in("x2") count,
            lateout("x0") ret,
            options(nostack),
        );
    }
    ret
}

/// Exit thread syscall: exit_thread(retval)
fn syscall_exit_thread(retval: usize) -> ! {
    unsafe {
        core::arch::asm!(
            "svc #0",
            in("x8") NR_EXIT_THREAD,
            in("x0") retval,
            options(noreturn),
        );
    }
    loop {}
}

// ---------------------------------------------------------------------------
// Panic handler
// ---------------------------------------------------------------------------

#[panic_handler]
fn panic(_info: &core::panic::PanicInfo) -> ! {
    loop {}
}