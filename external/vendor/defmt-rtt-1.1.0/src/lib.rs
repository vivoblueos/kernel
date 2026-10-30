//! [`defmt`](https://github.com/knurling-rs/defmt) global logger over RTT.
//!
//! NOTE when using this crate it's not possible to use (link to) the
//! `rtt-target` crate
//!
//! To use this crate, link to it by importing it somewhere in your project.
//!
//! ```
//! // src/main.rs or src/bin/my-app.rs
//! use defmt_rtt as _;
//! ```
//!
//! # Blocking/Non-blocking
//!
//! `probe-rs` puts RTT into blocking-mode, to avoid losing data.
//!
//! As an effect this implementation may block forever if `probe-rs` disconnects
//! at runtime. This is because the RTT buffer will fill up and writing will
//! eventually halt the program execution.
//!
//! `defmt::flush` would also block forever in that case.
//!
//! If losing data is not an concern you can disable blocking mode by enabling
//! the feature `disable-blocking-mode`
//!
//! # Critical section implementation
//!
//! This crate uses
//! [`critical-section`](https://github.com/rust-embedded/critical-section) to
//! ensure only one thread is writing to the buffer at a time. You must import a
//! crate that provides a `critical-section` implementation suitable for the
//! current target. See the `critical-section` README for details.
//!
//! For example, for single-core privileged-mode Cortex-M targets, you can add
//! the following to your Cargo.toml.
//!
//! ```toml
//! [dependencies]
//! cortex-m = { version = "0.7.6", features = ["critical-section-single-core"]}
//! ```

#![no_std]

mod channel;
mod consts;

use core::{
    cell::UnsafeCell,
    sync::atomic::{AtomicBool, AtomicUsize, Ordering},
};

use crate::{channel::Channel, consts::BUF_SIZE};

/// The relevant bits in the mode field in the Header
const MODE_MASK: usize = 0b11;

/// Block the application if the RTT buffer is full, wait for the host to read data.
const MODE_BLOCK_IF_FULL: usize = 2;

/// Don't block if the RTT buffer is full. Truncate data to output as much as fits.
const MODE_NON_BLOCKING_TRIM: usize = 1;

/// The defmt global logger
///
/// The defmt crate requires that this be a unit type, so our state is stored in
/// [`RTT_ENCODER`] instead.
#[defmt::global_logger]
struct Logger;

/// Our defmt encoder state
static RTT_ENCODER: RttEncoder = RttEncoder::new();

/// Our shared header structure.
///
/// The host will read this structure so it must be arranged as expected.
///
/// NOTE the `rtt-target` API is too permissive. It allows writing arbitrary
/// data to any channel (`set_print_channel` + `rprint*`) and that can corrupt
/// defmt log frames. So we declare the RTT control block here and make it
/// impossible to use `rtt-target` together with this crate.
#[no_mangle]
static _SEGGER_RTT: Header = Header {
    id: *b"SEGGER RTT\0\0\0\0\0\0",
    max_up_channels: 1,
    max_down_channels: 0,
    up_channel: Channel {
        name: NAME.as_ptr(),
        buffer: BUFFER.get(),
        size: BUF_SIZE,
        write: AtomicUsize::new(0),
        read: AtomicUsize::new(0),
        flags: AtomicUsize::new(MODE_NON_BLOCKING_TRIM),
    },
};

/// Report whether the SEGGER RTT up channel is in blocking mode.
///
/// Returns true if the mode bitfield within the flags value has been set to
/// `SEGGER_RTT_MODE_BLOCK_IF_FIFO_FULL`.
///
/// Currently we start-up in non-blocking mode, so if it's been set to blocking
/// mode then the connected client (e.g. probe-rs) must have done it.
pub fn in_blocking_mode() -> bool {
    (_SEGGER_RTT.up_channel.flags.load(Ordering::Relaxed) & MODE_MASK) == MODE_BLOCK_IF_FULL
}

/// Our shared buffer
#[cfg_attr(target_os = "macos", link_section = ".uninit,defmt-rtt.BUFFER")]
#[cfg_attr(not(target_os = "macos"), link_section = ".uninit.defmt-rtt.BUFFER")]
static BUFFER: Buffer = Buffer::new();

/// The name of our channel.
///
/// This is in a data section, so the whole RTT header can be read from RAM.
/// This is useful if flash access gets disabled by the firmware at runtime.
#[cfg_attr(target_os = "macos", link_section = ".data,defmt-rtt.NAME")]
#[cfg_attr(not(target_os = "macos"), link_section = ".data.defmt-rtt.NAME")]
static NAME: [u8; 6] = *b"defmt\0";

struct RttEncoder {
    /// A boolean lock
    ///
    /// Is `true` when `acquire` has been called and we have exclusive access to
    /// the rest of this structure.
    taken: AtomicBool,
    /// We need to remember this to exit a critical section
    cs_restore: UnsafeCell<critical_section::RestoreState>,
    /// A defmt::Encoder for encoding frames
    encoder: UnsafeCell<defmt::Encoder>,
}

impl RttEncoder {
    /// Create a new semihosting-based defmt-encoder
    const fn new() -> RttEncoder {
        RttEncoder {
            taken: AtomicBool::new(false),
            cs_restore: UnsafeCell::new(critical_section::RestoreState::invalid()),
            encoder: UnsafeCell::new(defmt::Encoder::new()),
        }
    }

    /// Acquire the defmt encoder.
    fn acquire(&self) {
        // safety: Must be paired with corresponding call to release(), see below
        let restore = unsafe { critical_section::acquire() };

        // NB: You can re-enter critical sections but we need to make sure
        // no-one does that.
        if self.taken.load(Ordering::Relaxed) {
            panic!("defmt logger taken reentrantly")
        }

        // no need for CAS because we are in a critical section
        self.taken.store(true, Ordering::Relaxed);

        // safety: accessing the cell is OK because we have acquired a critical
        // section.
        unsafe {
            self.cs_restore.get().write(restore);
            let encoder: &mut defmt::Encoder = &mut *self.encoder.get();
            encoder.start_frame(|b| {
                _SEGGER_RTT.up_channel.write_all(b);
            });
        }
    }

    /// Write bytes to the defmt encoder.
    ///
    /// # Safety
    ///
    /// Do not call unless you have called `acquire`.
    unsafe fn write(&self, bytes: &[u8]) {
        // safety: accessing the cell is OK because we have acquired a critical
        // section.
        unsafe {
            let encoder: &mut defmt::Encoder = &mut *self.encoder.get();
            encoder.write(bytes, |b| {
                _SEGGER_RTT.up_channel.write_all(b);
            });
        }
    }

    /// Flush the encoder
    ///
    /// # Safety
    ///
    /// Do not call unless you have called `acquire`.
    unsafe fn flush(&self) {
        // safety: accessing the `&'static _` is OK because we have acquired a
        // critical section.
        _SEGGER_RTT.up_channel.flush();
    }

    /// Release the defmt encoder.
    ///
    /// # Safety
    ///
    /// Do not call unless you have called `acquire`. This will release
    /// your lock - do not call `flush` and `write` until you have done another
    /// `acquire`.
    unsafe fn release(&self) {
        if !self.taken.load(Ordering::Relaxed) {
            panic!("defmt release out of context")
        }

        // safety: accessing the cell is OK because we have acquired a critical
        // section.
        unsafe {
            let encoder: &mut defmt::Encoder = &mut *self.encoder.get();
            encoder.end_frame(|b| {
                _SEGGER_RTT.up_channel.write_all(b);
            });
            let restore = self.cs_restore.get().read();
            self.taken.store(false, Ordering::Relaxed);
            // paired with exactly one acquire call
            critical_section::release(restore);
        }
    }
}

unsafe impl Sync for RttEncoder {}

unsafe impl defmt::Logger for Logger {
    fn acquire() {
        RTT_ENCODER.acquire();
    }

    unsafe fn write(bytes: &[u8]) {
        unsafe {
            RTT_ENCODER.write(bytes);
        }
    }

    unsafe fn flush() {
        unsafe {
            RTT_ENCODER.flush();
        }
    }

    unsafe fn release() {
        unsafe {
            RTT_ENCODER.release();
        }
    }
}

#[repr(C)]
struct Header {
    id: [u8; 16],
    max_up_channels: usize,
    max_down_channels: usize,
    up_channel: Channel,
}

unsafe impl Sync for Header {}

struct Buffer {
    inner: UnsafeCell<[u8; BUF_SIZE]>,
}

impl Buffer {
    const fn new() -> Buffer {
        Buffer {
            inner: UnsafeCell::new([0; BUF_SIZE]),
        }
    }

    const fn get(&self) -> *mut u8 {
        self.inner.get() as _
    }
}

unsafe impl Sync for Buffer {}
