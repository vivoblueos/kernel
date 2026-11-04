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

//! The user images the kernel carries inside itself, and the boot-time run
//! that proves the U-mode path works on real hardware.
//!
//! # Why embed instead of load from disk
//!
//! A run of QEMU has no disk. The alternative — a build step that bakes the
//! images into the filesystem image — puts the program out of reach of the
//! one thing that needs it: a kernel that wants to show, on every boot, that
//! its own loader and trap path work end to end. Embedding keeps the fixture
//! and the check together, and costs ~9 KiB.
//!
//! # Why the program's job is to exit with 7
//!
//! Reaching `write` proves the ELF loader mapped a segment at its link
//! address and the trap path dropped to U-mode with a usable stack. Exiting
//! with a specific status proves the *return* path: the `ecall` came back
//! through `handle_ecall`, `exit_group` set a status, the process became a
//! zombie, and `waitpid` in the parent collected it. A program that printed
//! and vanished would prove less.
//!
//! The images are produced by `tools/build_user_programs.sh`; the numbers they
//! use for syscall numbers are generated from [`blueos_header::syscalls::NR`],
//! so the two sides cannot drift.

use crate::error::{code, Error};
use crate::process::ProcessManager;
use alloc::{boxed::Box, sync::Arc};
use core::ffi::c_int;

/// `hello`, the smallest program that exercises the whole path.
///
/// Built from `apps/user/hello/hello.c` at a fixed link address; see
/// [`super::USER_IMAGE_BASE`].
pub static HELLO: &[u8] = include_bytes!("prog/hello.elf");

/// `proc`, a freestanding program that drives the whole process model:
/// `fork`, `getpid`, `getppid`, `waitpid`, `execve` and `exit_group`.
///
/// The POSIX conformance harness runs in M-mode kernel threads, where there is
/// no current process and these calls return `EPERM`, so they cannot be tested
/// there. `proc` runs as a real U-mode process - the only context in which the
/// process model means anything - and reports its result as an exit status.
pub static PROC: &[u8] = include_bytes!("prog/proc.elf");

/// `posix_u`, the U-mode half of the POSIX harness (DF-17).
///
/// The cases in `librs/tests/posix` run as M-mode kernel threads, where
/// `vfs::uptr` treats caller pointers as kernel addresses. This program asks
/// the same questions from a real process: an unmapped pointer must be
/// `EFAULT` from the fault path, and a `sigaction`/`raise` pair must run the
/// handler in U-mode and return through `sigreturn`.
pub static POSIX_U: &[u8] = include_bytes!("prog/posix_u.elf");

/// Directory the images are installed into.
pub const BIN_DIR: &str = "/bin";

/// Path `hello` is installed at and started from.
pub const HELLO_PATH: &str = "/bin/hello";

/// Status `hello` exits with. Mirrors `EXIT_CODE` in `hello.c`.
pub const HELLO_EXIT: i32 = 7;

/// Path `proc` is installed at and started from.
pub const PROC_PATH: &str = "/bin/proc";

/// Path `posix_u` is installed at and started from.
pub const POSIX_U_PATH: &str = "/bin/posix_u";

/// Status `proc` exits with on success: every assertion in `proc.c` held.
/// Mirrors the `failures == 0` path at the end of `_start`.
pub const PROC_EXIT: i32 = 0;

/// Write the embedded images into the filesystem.
///
/// Idempotent: the images are small, and rewriting them costs less than
/// deciding whether an existing copy is the right one.
///
/// Installs both embedded images. `install_file` refuses an existing file, so a
/// second caller (the two smoke threads share one boot) must tolerate
/// `EEXIST` rather than fail.
pub fn install() -> Result<(), Error> {
    crate::vfs::ensure_dir(BIN_DIR)?;
    install_idempotent(HELLO_PATH, HELLO)?;
    install_idempotent(PROC_PATH, PROC)?;
    Ok(())
}

/// `install_file`, but a file that is already present counts as success - the
/// embedded images are identical on every boot, so an earlier installer did
/// the same job.
fn install_idempotent(path: &str, bytes: &[u8]) -> Result<(), Error> {
    match crate::vfs::install_file(path, bytes) {
        Ok(()) => Ok(()),
        Err(e) if e == code::EEXIST => Ok(()),
        Err(e) => Err(e),
    }
}

/// Start the smoke program in a thread of its own.
///
/// A thread rather than the boot path itself because the run *blocks* in
/// `waitpid`, and the boot thread reaches the scheduler only after this
/// returns. Blocking the last thread before `start_schedule` would hang the
/// machine instead of testing it.
pub fn start_smoke() {
    let body = Box::new(smoke_body);
    let stack = match crate::thread::Stack::from_size(
        blueos_kconfig::CONFIG_MAIN_THREAD_STACK_SIZE as usize,
    ) {
        Some(s) => s,
        None => {
            crate::kearly_println!("user: no stack for the smoke thread");
            return;
        }
    };
    let node = crate::thread::Builder::new(crate::thread::Entry::Closure(body))
        .set_stack(stack)
        .start();
    // Its own process, so `waitpid` has a child and the thread's lifetime is
    // not tied to the root process's.
    let root = ProcessManager::get().root_process();
    match ProcessManager::get().create_process(Arc::downgrade(root)) {
        Ok(proc) => {
            if !proc.add_thread(node) {
                crate::kearly_println!("user: smoke thread could not join its process");
            }
        }
        Err(e) => crate::kearly_println!("user: could not create the smoke process: {}", e),
    }
}

/// Start `proc` in a thread of its own and reap it, mirroring [`start_smoke`].
///
/// `proc` is the evidence for the librs process wrappers and the kernel's
/// process model, so it is gated to the same targets that actually run user
/// programs. It installs both `/bin/proc` and `/bin/hello`, because `proc`
/// reaps children that `execve` `/bin/hello` - a missing image would make the
/// execve test fail for the wrong reason.
#[cfg(all(enable_vfs, target_arch = "riscv64", enable_user_programs))]
pub fn start_proc_smoke() {
    let body = Box::new(proc_body);
    let stack = match crate::thread::Stack::from_size(
        blueos_kconfig::CONFIG_MAIN_THREAD_STACK_SIZE as usize,
    ) {
        Some(s) => s,
        None => {
            crate::kearly_println!("user: no stack for the proc smoke thread");
            return;
        }
    };
    let node = crate::thread::Builder::new(crate::thread::Entry::Closure(body))
        .set_stack(stack)
        .start();
    let root = ProcessManager::get().root_process();
    match ProcessManager::get().create_process(Arc::downgrade(root)) {
        Ok(proc) => {
            if !proc.add_thread(node) {
                crate::kearly_println!("user: proc smoke thread could not join its process");
            }
        }
        Err(e) => crate::kearly_println!("user: could not create the proc smoke process: {}", e),
    }
}

#[cfg(all(enable_vfs, target_arch = "riscv64", enable_user_programs))]
fn proc_body() {
    if let Err(e) = install() {
        crate::kearly_println!("user: proc smoke could not install images: {}", e);
        crate::scheduler::retire_me();
        return;
    }
    let pid = match super::spawn_path(PROC_PATH) {
        Ok(pid) => pid,
        Err(e) => {
            crate::kearly_println!("user: proc smoke could not spawn: {}", e);
            crate::scheduler::retire_me();
            return;
        }
    };
    let mut status: c_int = 0;
    let reaped = super::sys_waitpid(pid.0 as c_int, &mut status as *mut c_int, 0);
    if reaped < 0 {
        crate::kearly_println!("user: proc smoke could not reap: errno {}", reaped);
    } else if (status >> 8) == PROC_EXIT {
        crate::kearly_println!(
            "user: proc smoke exited with {} — process model (fork/getpid/getppid/waitpid/execve) verified",
            status >> 8
        );
    } else {
        crate::kearly_println!(
            "user: proc smoke exited with {} but {} was expected",
            status >> 8,
            PROC_EXIT
        );
    }
    crate::scheduler::retire_me();
}

/// C entry point used by the POSIX harness (`librs/tests/posix/runner.c`).
///
/// The probe belongs to the image whose checker asserts on it - the POSIX
/// harness, which runs long enough for `POSIX-U-DONE` to arrive before
/// `POSIX-CHECK-DONE`. Starting it from `boot` as well would interleave its
/// markers with the shell smoke's console expectations and is pointless there;
/// this symbol is referenced only by the POSIX runner. A no-op where user
/// programs do not exist keeps the C side board-independent.
#[no_mangle]
pub extern "C" fn posix_start_u_probe() {
    #[cfg(all(enable_vfs, target_arch = "riscv64", enable_user_programs))]
    start_posix_u_smoke();
}

/// Start `posix_u` in a thread of its own and reap it, mirroring
/// [`start_proc_smoke`].
///
/// The POSIX harness runs in M-mode, so this is the only automated evidence
/// that `vfs::uptr` really walks the caller's page table and that an
/// unmapped pointer becomes `EFAULT` instead of a kernel read.
#[cfg(all(enable_vfs, target_arch = "riscv64", enable_user_programs))]
pub fn start_posix_u_smoke() {
    let body = Box::new(posix_u_body);
    let stack = match crate::thread::Stack::from_size(
        blueos_kconfig::CONFIG_MAIN_THREAD_STACK_SIZE as usize,
    ) {
        Some(s) => s,
        None => {
            crate::kearly_println!("user: no stack for the posix-u smoke thread");
            return;
        }
    };
    let node = crate::thread::Builder::new(crate::thread::Entry::Closure(body))
        .set_stack(stack)
        .start();
    let root = ProcessManager::get().root_process();
    match ProcessManager::get().create_process(Arc::downgrade(root)) {
        Ok(proc) => {
            if !proc.add_thread(node) {
                crate::kearly_println!("user: posix-u smoke thread could not join its process");
            }
        }
        Err(e) => crate::kearly_println!("user: could not create the posix-u smoke process: {}", e),
    }
}

#[cfg(all(enable_vfs, target_arch = "riscv64", enable_user_programs))]
fn posix_u_body() {
    if let Err(e) = install() {
        crate::kearly_println!("user: posix-u smoke could not install images: {}", e);
        crate::scheduler::retire_me();
        return;
    }
    // Installed here rather than in `install()`: the shell smoke shares that
    // function, and the probe is neither needed nor asserted there.
    if let Err(e) = install_idempotent(POSIX_U_PATH, POSIX_U) {
        crate::kearly_println!("user: posix-u smoke could not install the probe: {}", e);
        crate::scheduler::retire_me();
        return;
    }
    let pid = match super::spawn_path(POSIX_U_PATH) {
        Ok(pid) => pid,
        Err(e) => {
            crate::kearly_println!("user: posix-u smoke could not spawn: {}", e);
            crate::scheduler::retire_me();
            return;
        }
    };
    let mut status: c_int = 0;
    let reaped = super::sys_waitpid(pid.0 as c_int, &mut status as *mut c_int, 0);
    if reaped < 0 {
        crate::kearly_println!("user: posix-u smoke could not reap: errno {}", reaped);
    } else if (status >> 8) == 0 {
        crate::kearly_println!(
            "user: posix-u smoke exited with 0 — U-mode uaccess/EFAULT/signal semantics verified"
        );
    } else {
        crate::kearly_println!(
            "user: posix-u smoke exited with {} but 0 was expected",
            status >> 8
        );
    }
    crate::scheduler::retire_me();
}

fn smoke_body() {
    match install_and_run() {
        Ok(status) if status == HELLO_EXIT => {
            crate::kearly_println!(
                "user: smoke program exited with {} as expected — U-mode path verified",
                status
            );
        }
        Ok(status) => {
            crate::kearly_println!(
                "user: smoke program exited with {} but {} was expected",
                status,
                HELLO_EXIT
            );
        }
        Err(errno) => {
            crate::kearly_println!("user: smoke program could not run: errno {}", errno);
        }
    }
    // Returning would hand control back to the thread trampoline, which is
    // free to reuse the stack; retiring is the explicit way to say this thread
    // is done and must never be scheduled again.
    crate::scheduler::retire_me();
}

/// Install, start and reap the smoke program, returning its exit status.
fn install_and_run() -> Result<i32, isize> {
    install().map_err(|e| e.to_errno() as isize)?;
    let pid = super::spawn_path(HELLO_PATH)?;
    let mut status: c_int = 0;
    let reaped = super::sys_waitpid(pid.0 as c_int, &mut status as *mut c_int, 0);
    if reaped < 0 {
        return Err(reaped);
    }
    if reaped != pid.0 as isize {
        return Err(code::ECHILD.to_errno() as isize);
    }
    // `waitpid` returns the *encoded* status: the exit code lives in bits
    // 8..16 so the low byte can say "died from a signal" instead.
    Ok(status >> 8)
}
