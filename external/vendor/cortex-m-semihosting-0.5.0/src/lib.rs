//! Semihosting for ARM Cortex-M processors
//!
//! # What is semihosting?
//!
//! "Semihosting is a mechanism that enables code running on an ARM target to communicate and use
//! the Input/Output facilities on a host computer that is running a debugger." - ARM
//!
//! # Interface
//!
//! This crate provides implementations of
//! [`core::fmt::Write`](https://doc.rust-lang.org/core/fmt/trait.Write.html), so you can use it,
//! in conjunction with
//! [`core::format_args!`](https://doc.rust-lang.org/core/macro.format_args.html) or the [`write!` macro](https://doc.rust-lang.org/core/macro.write.html), for user-friendly construction and printing of formatted strings.
//!
//! Since semihosting operations are modeled as [system calls][sc], this crate exposes an untyped
//! `syscall!` interface just like the [`sc`] crate does.
//!
//! [sc]: https://en.wikipedia.org/wiki/System_call
//! [`sc`]: https://crates.io/crates/sc
//!
//! # Forewarning
//!
//! Semihosting operations are *very* slow. Like, each WRITE operation can take hundreds of
//! milliseconds.
//!
//! # Example
//!
//! ## Using `hio::hstdout`
//!
//! This example will demonstrate how to print formatted strings.
//!
//! ```no_run
//! use cortex_m_semihosting::hio;
//! use core::fmt::Write;
//!
//! // This function will be called by the application
//! fn print() -> Result<(), core::fmt::Error> {
//!     let mut stdout = hio::hstdout().map_err(|_| core::fmt::Error)?;
//!     let language = "Rust";
//!     let ranking = 1;
//!
//!     write!(stdout, "{} on embedded is #{}!", language, ranking)?;
//!
//!     Ok(())
//! }
//! ```
//!
//! On the host side:
//!
//! ``` text
//! $ openocd -f $INTERFACE -f $TARGET -l /tmp/openocd.log
//! Open On-Chip Debugger 0.9.0 (2016-04-27-23:18)
//! Licensed under GNU GPL v2
//! For bug reports, read
//!         http://openocd.org/doc/doxygen/bugs.html
//! # the command will block at this point
//! ```
//!
//! The OpenOCD logs will be redirected to `/tmp/openocd.log`. You can view those logs in "real
//! time" using `tail`
//!
//! ``` text
//! $ tail -f /tmp/openocd.log
//! Info : Unable to match requested speed 1000 kHz, using 950 kHz
//! Info : Unable to match requested speed 1000 kHz, using 950 kHz
//! Info : clock speed 950 kHz
//! Info : STLINK v1 JTAG v11 API v2 SWIM v0 VID 0x0483 PID 0x3744
//! Info : using stlink api v2
//! Info : nrf51.cpu: hardware has 4 breakpoints, 2 watchpoints
//! ```
//!
//! Alternatively you could omit the `-l` flag from the `openocd` call, and the `tail -f` command
//! but the OpenOCD output will have intermingled in it logs from its normal operation.
//!
//! Then, we run the program:
//!
//! ``` text
//! $ arm-none-eabi-gdb hello-world
//! (gdb) # Connect to OpenOCD
//! (gdb) target remote :3333
//!
//! (gdb) # Enable OpenOCD's semihosting support
//! (gdb) monitor arm semihosting enable
//!
//! (gdb) # Flash the program
//! (gdb) load
//!
//! (gdb) # Run the program
//! (gdb) continue
//! ```
//!
//! And you'll see the output under OpenOCD's terminal
//!
//! ``` text
//! # openocd -f $INTERFACE -f $TARGET -l /tmp/openocd.log
//! (..)
//! Rust on embedded is #1!
//! ```
//! ## Using the syscall interface
//!
//! This example will show how to print "Hello, world!" on the host.
//!
//! Target program:
//!
//! ```no_run
//! use cortex_m_semihosting::syscall;
//!
//! // This function will be called by the application
//! fn print() {
//!     // File descriptor (on the host)
//!     const STDOUT: usize = 1; // NOTE the host stdout may not always be fd 1
//!     static MSG: &'static [u8] = b"Hello, world!\n";
//!
//!     // Signature: fn write(fd: usize, ptr: *const u8, len: usize) -> usize
//!     let r = unsafe { syscall!(WRITE, STDOUT, MSG.as_ptr(), MSG.len()) };
//! }
//! ```
//! Output and monitoring proceed as in the above example.
//!
//! ## The `dbg!` macro
//!
//! Analogous to [`std::dbg`](https://doc.rust-lang.org/std/macro.dbg.html) the macro
//! `dbg!` returns a given expression and prints it using `heprintln!` including context
//! for quick and dirty debugging.
//!
//! Panics if `heprintln!` returns an error.
//!
//! Example:
//!
//! ```no_run
//! const UUID: *mut u32 = 0x0009_FC70 as *mut u32;
//! dbg!(UUID);
//! let mut uuid: [u32; 4] = [0; 4];
//! for i in 0..4 {
//!     dbg!(i);
//!     uuid[i] = unsafe { dbg!(UUID.offset(i as isize).read_volatile()) };
//! }
//! ```
//! outputs
//! ```text
//! [examples/semihosting.rs:37] UUID = 0x0009fc70
//! [examples/semihosting.rs:40] i = 0
//! [examples/semihosting.rs:41] UUID.offset(i as isize).read_volatile() = 3370045464
//! [examples/semihosting.rs:40] i = 1
//! [examples/semihosting.rs:41] UUID.offset(i as isize).read_volatile() = 1426218275
//! [examples/semihosting.rs:40] i = 2
//! [examples/semihosting.rs:41] UUID.offset(i as isize).read_volatile() = 2422621116
//! [examples/semihosting.rs:40] i = 3
//! [examples/semihosting.rs:41] UUID.offset(i as isize).read_volatile() = 1044138593
//! ```
//!
//! # Optional features
//!
//! ## `jlink-quirks`
//!
//! When this feature is enabled, return values above `0xfffffff0` from semihosting operation
//! `SYS_WRITE` (0x05) are interpreted as if the entire buffer had been written. The current
//! latest version 6.48b of J-Link exhibits such behaviour, causing a panic if this feature
//! is not enabled.
//!
//! ## `no-semihosting`
//!
//! When this feature is enabled, the underlying system calls to `bkpt` are patched out.
//!
//! # Reference
//!
//! For documentation about the semihosting operations, check:
//!
//! 'Chapter 8 - Semihosting' of the ['ARM Compiler toolchain Version 5.0'][pdf]
//! manual.
//!
//! [pdf]: http://infocenter.arm.com/help/topic/com.arm.doc.dui0471e/DUI0471E_developing_for_arm_processors.pdf

#![deny(missing_docs)]
#![no_std]

#[macro_use]
mod macros;

pub mod debug;
#[doc(hidden)]
pub mod export;
pub mod hio;
pub mod nr;

/// Performs a semihosting operation, takes a pointer to an argument block
#[inline(always)]
pub unsafe fn syscall<T>(nr: usize, arg: &T) -> usize {
    syscall1(nr, arg as *const T as usize)
}

/// Performs a semihosting operation, takes one integer as an argument
#[inline(always)]
pub unsafe fn syscall1(_nr: usize, _arg: usize) -> usize {
    match () {
        #[cfg(all(thumb, not(feature = "no-semihosting")))]
        () => {
            use core::arch::asm;
            let mut nr = _nr as u32;
            let arg = _arg as u32;
            asm!("bkpt #0xab", inout("r0") nr, in("r1") arg, options(nostack, preserves_flags));
            nr as usize
        }
        #[cfg(all(thumb, feature = "no-semihosting"))]
        () => 0,
        #[cfg(not(thumb))]
        () => unimplemented!(),
    }
}
