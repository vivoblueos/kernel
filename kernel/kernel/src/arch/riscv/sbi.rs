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

//! The SBI layer: the interface between the kernel and the machine-level
//! firmware that owns the machine's resources.
//!
//! # Why this exists
//!
//! The kernel runs in M-mode today, so it owns every machine resource
//! outright: it writes `mtimecmp`, it writes `msip`, it touches the UART. That
//! works, but it is exactly the arrangement that leaves the kernel with no
//! higher-privilege layer to fall back on - a kernel bug that corrupts a
//! machine register cannot be recovered from, because the kernel *is* the
//! most privileged thing on the chip.
//!
//! The migration to a layered design (M-mode firmware / S-mode kernel /
//! U-mode programs) fixes that by putting a thin firmware layer between the
//! kernel and the machine. That layer exposes its services through the
//! Supervisor Binary Interface, and this module is the kernel's side of that
//! interface.
//!
//! See `S_MODE_MIGRATION.md` for the full plan.
//!
//! # The shape of the interface
//!
//! SBI has two sides, and this module keeps them apart on purpose:
//!
//! * The **client** side ([`send_ipi`], [`clear_ipi`], ...) is what the rest of
//!   the kernel calls. It is written the way a caller writes any SBI call:
//!   build a request, get a result back.
//! * The **server** side ([`Firmware`], [`dispatch`], [`firmware_entry`]) is
//!   what answers such a request. It is deliberately ignorant of *how* the
//!   request arrived.
//!
//! Keeping them separate is what makes the migration possible. Today the two
//! are wired together directly - the client calls the server's implementation
//! in the same address space, which is what "pass-through" means here. Once
//! the kernel moves to S-mode, the client will issue an `ecall` instead and
//! the server will run in the M-mode firmware, but neither side has to change:
//! only the wire between them does.
//!
//! # The wire
//!
//! The register encoding follows the SBI specification:
//!
//! | Register | Meaning |
//! |----------|---------|
//! | `a7`     | extension ID (EID) |
//! | `a6`     | function ID (FID) within the extension |
//! | `a0`-`a5`| arguments |
//!
//! and a call returns an error code in `a0` and a value in `a1`. All other
//! registers must survive the call.
//!
//! The client already goes through that encoding - [`SbiCall::encode`] and
//! [`SbiCall::decode`] - even though the transport is a direct call today.
//! That is deliberate: it means the register layout is exercised by every
//! call the kernel makes, so the day the transport becomes an `ecall` there
//! is no untested path left to break.
//!
//! [`dispatch`] implements the dispatch rules. It is pure logic over plain
//! integers, so it is exercised by the unit tests at the bottom of this file
//! rather than only by running the kernel.

use blueos_hal::clock::Clock;

/// Extension IDs (EID).
///
/// These are the identifiers from the SBI specification. The values are
/// chosen so that a register dump reads as ASCII: `0x54494d45` is "TIME".
pub(crate) mod ext {
    /// Base extension: version queries and extension probing.
    pub(crate) const BASE: usize = 0x10;
    /// Timer extension: programs the next timer event.
    pub(crate) const TIME: usize = 0x5449_4d45;
    /// Inter-processor interrupt extension ("sPI" in ASCII).
    pub(crate) const IPI: usize = 0x0073_5049;
    /// Hart state management extension: starting harts ("HSM" in ASCII).
    pub(crate) const HSM: usize = 0x0048_534d;
    /// System reset extension.
    pub(crate) const SRST: usize = 0x5352_5354;
    /// Debug console extension: character output.
    pub(crate) const DBCN: usize = 0x4442_434e;
}

/// Function IDs (FID) within an extension.
pub(crate) mod fid {
    /// `BASE`: read the implemented specification version.
    pub(crate) const BASE_GET_SPEC_VERSION: usize = 0;
    /// `BASE`: probe whether an extension is implemented.
    pub(crate) const BASE_PROBE_EXT: usize = 3;
    /// `TIME`: set the next timer event.
    pub(crate) const TIME_SET_TIMER: usize = 0;
    /// `IPI`: send a software interrupt to a set of harts.
    pub(crate) const IPI_SEND_IPI: usize = 0;
    /// `IPI`: clear a previously sent software interrupt.
    ///
    /// The specification's IPI extension only defines `send_ipi`; clearing is
    /// a legacy operation (legacy EID `0x03`). It is kept here because the
    /// kernel needs both directions - it raises an IPI to wake another hart
    /// and has to take it back down afterwards - and because the CLINT's
    /// per-hart software interrupt registers need both halves anyway.
    pub(crate) const IPI_CLEAR_IPI: usize = 1;
    /// `HSM`: start a hart at a given address.
    pub(crate) const HSM_HART_START: usize = 0;
    /// `SRST`: reset the system.
    pub(crate) const SRST_SYSTEM_RESET: usize = 0;
    /// `DBCN`: write one character to the debug console.
    pub(crate) const DBCN_PUTCHAR: usize = 0;
}

/// Error codes returned in `a0`.
///
/// The values are the ones the specification defines.
pub(crate) mod err {
    /// The call succeeded.
    pub(crate) const SUCCESS: isize = 0;
    /// The call failed for an unspecified reason.
    pub(crate) const FAILED: isize = -1;
    /// The requested function is not implemented.
    pub(crate) const NOT_SUPPORTED: isize = -2;
    /// An argument was invalid.
    pub(crate) const INVALID_PARAM: isize = -3;
    /// The caller is not allowed to make this call.
    pub(crate) const DENIED: isize = -4;
    /// A pointer argument was invalid.
    pub(crate) const INVALID_ADDRESS: isize = -5;
}

/// The number of argument registers an SBI call carries (`a0`..`a5`).
const ARG_COUNT: usize = 6;

/// The number of registers an SBI call occupies (`a0`..`a7`).
const REG_COUNT: usize = 8;

/// The number of harts this kernel knows about.
const NUM_CORES: usize = super::NUM_CORES;

/// The mask of harts this kernel has.
///
/// Bit `n` stands for hart `n`, so this is all ones for the low
/// [`NUM_CORES`] bits.
const HART_MASK: usize = if NUM_CORES >= usize::BITS as usize {
    usize::MAX
} else {
    (1usize << NUM_CORES) - 1
};

/// An error returned by a firmware operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SbiError {
    /// The operation failed for an unspecified reason.
    Failed,
    /// The operation is not implemented.
    NotSupported,
    /// An argument was invalid.
    InvalidParam,
    /// The caller is not allowed to make this call.
    Denied,
    /// A pointer argument was invalid.
    InvalidAddress,
}

impl SbiError {
    /// The wire representation of this error.
    pub(crate) const fn code(self) -> isize {
        match self {
            SbiError::Failed => err::FAILED,
            SbiError::NotSupported => err::NOT_SUPPORTED,
            SbiError::InvalidParam => err::INVALID_PARAM,
            SbiError::Denied => err::DENIED,
            SbiError::InvalidAddress => err::INVALID_ADDRESS,
        }
    }

    /// The error a wire code stands for.
    ///
    /// `None` for a code that is not an error - success, or a code this
    /// implementation does not know.
    pub(crate) const fn from_code(code: isize) -> Option<SbiError> {
        match code {
            err::FAILED => Some(SbiError::Failed),
            err::NOT_SUPPORTED => Some(SbiError::NotSupported),
            err::INVALID_PARAM => Some(SbiError::InvalidParam),
            err::DENIED => Some(SbiError::Denied),
            err::INVALID_ADDRESS => Some(SbiError::InvalidAddress),
            _ => None,
        }
    }
}

/// The result of an SBI call: an error code and a value.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SbiRet {
    /// `0` on success, a negative error code otherwise.
    pub(crate) error: isize,
    /// The call's return value; meaningless when `error` is non-zero.
    pub(crate) value: usize,
}

impl SbiRet {
    /// A successful result carrying `value`.
    pub(crate) const fn ok(value: usize) -> SbiRet {
        SbiRet {
            error: err::SUCCESS,
            value,
        }
    }

    /// A failed result.
    pub(crate) const fn err(error: SbiError) -> SbiRet {
        SbiRet {
            error: error.code(),
            value: 0,
        }
    }

    /// Whether the call succeeded.
    #[allow(dead_code)]
    pub(crate) const fn is_ok(self) -> bool {
        self.error == err::SUCCESS
    }
}

/// An SBI request, before it is put on the wire.
///
/// This is the client's view of a call: an extension, a function within it,
/// and the arguments. [`encode`] turns it into the register layout, and
/// [`decode`] turns a register layout back into it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SbiCall {
    /// The extension being called.
    pub(crate) ext: usize,
    /// The function within the extension.
    pub(crate) fid: usize,
    /// The arguments, in `a0`..`a5` order.
    pub(crate) args: [usize; ARG_COUNT],
}

impl SbiCall {
    /// Builds a request.
    pub(crate) const fn new(ext: usize, fid: usize, args: [usize; ARG_COUNT]) -> SbiCall {
        SbiCall { ext, fid, args }
    }

    /// Encodes the request into the SBI register layout.
    ///
    /// The returned array is indexed by register number: index 0 is `a0`, so
    /// index 6 is `a6` (the function ID) and index 7 is `a7` (the extension
    /// ID).
    pub(crate) fn encode(&self) -> [usize; REG_COUNT] {
        let mut regs = [0usize; REG_COUNT];
        let mut i = 0;
        while i < ARG_COUNT {
            regs[i] = self.args[i];
            i += 1;
        }
        regs[6] = self.fid;
        regs[7] = self.ext;
        regs
    }

    /// Decodes a request from the SBI register layout.
    ///
    /// The layout is taken by value: the frame is eight words, and copying
    /// it keeps the decode free of aliasing questions.
    pub(crate) fn decode(regs: [usize; REG_COUNT]) -> SbiCall {
        let mut args = [0usize; ARG_COUNT];
        let mut i = 0;
        while i < ARG_COUNT {
            args[i] = regs[i];
            i += 1;
        }
        SbiCall {
            ext: regs[7],
            fid: regs[6],
            args,
        }
    }
}

/// The machine-level services a firmware layer has to offer.
///
/// This is the server side of the interface. An implementation reaches the
/// hardware on behalf of the kernel; the kernel never touches the machine
/// resources behind the firmware's back.
///
/// The methods mirror the SBI functions one-for-one, except that they return
/// a Rust [`SbiError`] instead of a wire code - turning errors into codes is
/// [`dispatch`]'s job.
pub(crate) trait Firmware {
    /// Programs the calling hart's next timer event.
    fn set_timer(&mut self, stime_value: u64) -> Result<(), SbiError>;

    /// Raises a software interrupt on every hart in `hart_mask`.
    fn send_ipi(&mut self, hart_mask: usize) -> Result<(), SbiError>;

    /// Takes back the software interrupt on every hart in `hart_mask`.
    fn clear_ipi(&mut self, hart_mask: usize) -> Result<(), SbiError>;

    /// Writes one character to the debug console.
    fn putchar(&mut self, ch: u8) -> Result<(), SbiError>;

    /// Starts a hart at `start_addr`.
    fn hart_start(
        &mut self,
        hart_id: usize,
        start_addr: u64,
        opaque: u64,
    ) -> Result<(), SbiError>;

    /// Resets the system.
    fn system_reset(&mut self, reset_type: u32, reason: u32) -> Result<(), SbiError>;
}

/// Dispatches an SBI request to a firmware implementation.
///
/// This is the server side's entry point. It owns the rules that are the same
/// whoever implements the hardware:
///
/// * an unknown extension or function is [`SbiError::NotSupported`], not a
///   silent no-op - a caller asking for something that does not exist has to
///   be able to tell;
/// * arguments are range-checked before they reach the hardware, so a
///   malformed hart number cannot turn into a write to an arbitrary place.
///
/// The argument checks live here rather than in the implementations on
/// purpose: the implementations are per-platform, and a platform that
/// forgot one would then be reachable with a bogus hart id.
pub(crate) fn dispatch(call: &SbiCall, fw: &mut impl Firmware) -> SbiRet {
    match call.ext {
        ext::BASE => dispatch_base(call),
        ext::TIME => dispatch_time(call, fw),
        ext::IPI => dispatch_ipi(call, fw),
        ext::HSM => dispatch_hsm(call, fw),
        ext::SRST => dispatch_srst(call, fw),
        ext::DBCN => dispatch_dbcn(call, fw),
        _ => SbiRet::err(SbiError::NotSupported),
    }
}

/// The `BASE` extension: version queries and probing.
///
/// Neither function touches the hardware, so this one needs no firmware
/// implementation.
fn dispatch_base(call: &SbiCall) -> SbiRet {
    match call.fid {
        fid::BASE_GET_SPEC_VERSION => {
            // The version is packed as major << 24 | minor, with the major
            // version in bits 24..30 and the minor version in bits 0..23.
            SbiRet::ok(2usize << 24)
        }
        fid::BASE_PROBE_EXT => {
            // Probing asks whether an extension exists; the answer is its
            // version, or zero if it is not implemented.
            let probed = call.args[0];
            let version = match probed {
                ext::BASE => 2,
                ext::TIME | ext::IPI | ext::HSM | ext::SRST | ext::DBCN => 1,
                _ => 0,
            };
            SbiRet::ok(version)
        }
        _ => SbiRet::err(SbiError::NotSupported),
    }
}

/// The `TIME` extension: programming the next timer event.
fn dispatch_time(call: &SbiCall, fw: &mut impl Firmware) -> SbiRet {
    match call.fid {
        fid::TIME_SET_TIMER => {
            let stime_value = call.args[0] as u64;
            match fw.set_timer(stime_value) {
                Ok(()) => SbiRet::ok(0),
                Err(e) => SbiRet::err(e),
            }
        }
        _ => SbiRet::err(SbiError::NotSupported),
    }
}

/// The `IPI` extension: software interrupts between harts.
fn dispatch_ipi(call: &SbiCall, fw: &mut impl Firmware) -> SbiRet {
    match call.fid {
        fid::IPI_SEND_IPI => {
            let hart_mask = call.args[0];
            if !hart_mask_is_valid(hart_mask) {
                return SbiRet::err(SbiError::InvalidParam);
            }
            match fw.send_ipi(hart_mask) {
                Ok(()) => SbiRet::ok(0),
                Err(e) => SbiRet::err(e),
            }
        }
        fid::IPI_CLEAR_IPI => {
            let hart_mask = call.args[0];
            if !hart_mask_is_valid(hart_mask) {
                return SbiRet::err(SbiError::InvalidParam);
            }
            match fw.clear_ipi(hart_mask) {
                Ok(()) => SbiRet::ok(0),
                Err(e) => SbiRet::err(e),
            }
        }
        _ => SbiRet::err(SbiError::NotSupported),
    }
}

/// The `HSM` extension: starting harts.
fn dispatch_hsm(call: &SbiCall, fw: &mut impl Firmware) -> SbiRet {
    match call.fid {
        fid::HSM_HART_START => {
            let hart_id = call.args[0];
            let start_addr = call.args[1] as u64;
            let opaque = call.args[2] as u64;
            if hart_id >= NUM_CORES {
                return SbiRet::err(SbiError::InvalidParam);
            }
            match fw.hart_start(hart_id, start_addr, opaque) {
                Ok(()) => SbiRet::ok(0),
                Err(e) => SbiRet::err(e),
            }
        }
        _ => SbiRet::err(SbiError::NotSupported),
    }
}

/// The `SRST` extension: resetting the system.
fn dispatch_srst(call: &SbiCall, fw: &mut impl Firmware) -> SbiRet {
    match call.fid {
        fid::SRST_SYSTEM_RESET => {
            let reset_type = call.args[0] as u32;
            let reason = call.args[1] as u32;
            // The specification defines shutdown, cold reboot and warm reboot.
            if reset_type > 2 {
                return SbiRet::err(SbiError::InvalidParam);
            }
            match fw.system_reset(reset_type, reason) {
                Ok(()) => SbiRet::ok(0),
                Err(e) => SbiRet::err(e),
            }
        }
        _ => SbiRet::err(SbiError::NotSupported),
    }
}

/// The `DBCN` extension: the debug console.
fn dispatch_dbcn(call: &SbiCall, fw: &mut impl Firmware) -> SbiRet {
    match call.fid {
        fid::DBCN_PUTCHAR => {
            let ch = call.args[0] as u8;
            match fw.putchar(ch) {
                Ok(()) => SbiRet::ok(0),
                Err(e) => SbiRet::err(e),
            }
        }
        _ => SbiRet::err(SbiError::NotSupported),
    }
}

/// Whether a hart mask names only harts this kernel has.
///
/// Bit `n` of the mask stands for hart `n`, so the mask is valid when every
/// set bit is below the hart count.
fn hart_mask_is_valid(hart_mask: usize) -> bool {
    hart_mask & !HART_MASK == 0
}

// ---------------------------------------------------------------------------
// The pass-through implementation
// ---------------------------------------------------------------------------

/// The firmware implementation that runs in the kernel's own address space.
///
/// This is the "pass-through" arrangement: the client calls the server
/// directly instead of trapping into a separate M-mode program. It exists so
/// that the interface is real and exercised before the privilege split
/// happens - the kernel calls [`send_ipi`] and friends exactly as it will
/// once the calls really do cross a privilege boundary.
///
/// Only the operations the kernel has a hardware path for are implemented
/// here. The rest report [`SbiError::NotSupported`], which is the honest
/// answer: a caller must be able to tell "not implemented" from "done".
pub(crate) struct PlatformFirmware;

impl Firmware for PlatformFirmware {
    fn set_timer(&mut self, stime_value: u64) -> Result<(), SbiError> {
        // The board's clock is the one and only owner of the timer register,
        // so the pass-through goes through it rather than poking the
        // register from here. When the timer moves behind real M-mode
        // firmware this call becomes the `ecall` and the board clock stays
        // where it is - on the firmware side of the boundary.
        crate::boards::ClockImpl::interrupt_at(stime_value);
        Ok(())
    }

    fn send_ipi(&mut self, hart_mask: usize) -> Result<(), SbiError> {
        for_each_hart(hart_mask, crate::boards::send_ipi);
        Ok(())
    }

    fn clear_ipi(&mut self, hart_mask: usize) -> Result<(), SbiError> {
        for_each_hart(hart_mask, crate::boards::clear_ipi);
        Ok(())
    }

    fn putchar(&mut self, ch: u8) -> Result<(), SbiError> {
        crate::console::write_console_uart(ch);
        Ok(())
    }

    fn hart_start(
        &mut self,
        _hart_id: usize,
        _start_addr: u64,
        _opaque: u64,
    ) -> Result<(), SbiError> {
        // Starting a secondary hart is what the M-mode firmware does today;
        // until the firmware layer exists there is nothing to call.
        Err(SbiError::NotSupported)
    }

    fn system_reset(&mut self, _reset_type: u32, _reason: u32) -> Result<(), SbiError> {
        // Resetting the machine is the firmware's job, and there is no
        // firmware yet.
        Err(SbiError::NotSupported)
    }
}

/// Runs `f` for every hart the mask selects.
///
/// The mask has already been range-checked by [`dispatch`], so no hart
/// outside this kernel can reach here.
fn for_each_hart(hart_mask: usize, mut f: impl FnMut(usize)) {
    let mut remaining = hart_mask & HART_MASK;
    while remaining != 0 {
        let hart = remaining.trailing_zeros() as usize;
        remaining &= remaining - 1;
        f(hart);
    }
}

// ---------------------------------------------------------------------------
// The firmware entry point
// ---------------------------------------------------------------------------

/// The M-mode side of an SBI call.
///
/// This is what the machine's trap handler calls when an SBI request
/// arrives. It takes the register frame the request arrived in, runs the
/// request, and hands back the register frame the caller should see: `a0`
/// carries the error code, `a1` the return value, and every other register
/// is preserved - the specification requires that, because the caller may
/// well be mid-way through something that depends on those registers.
///
/// Today the "trap handler" is the client itself ([`call`]), because both
/// sides live in the same address space. When the kernel moves to S-mode,
/// this function is what the M-mode firmware runs, and the client reaches
/// it with an `ecall`.
pub(crate) fn firmware_entry(regs: &[usize; REG_COUNT]) -> [usize; REG_COUNT] {
    let request = SbiCall::decode(*regs);
    let mut fw = PlatformFirmware;
    let ret = dispatch(&request, &mut fw);

    let mut out = *regs;
    // The error code travels as a register, so it keeps its bit pattern.
    out[0] = ret.error as usize;
    out[1] = ret.value;
    out
}

// ---------------------------------------------------------------------------
// The client side
// ---------------------------------------------------------------------------

/// Issues one SBI request against the pass-through firmware.
///
/// This is where the client and the server meet. The request is encoded into
/// the register layout and handed to [`firmware_entry`], exactly as it will
/// be when the transport becomes an `ecall`: the only thing that changes is
/// that the frame goes out through a trap instead of a function call.
///
/// Going through the encoding even now is what keeps the wire honest. The
/// layout is exercised by every call the kernel makes, so there is no
/// encoding corner that is only discovered once the kernel runs in S-mode.
fn call(ext: usize, fid: usize, args: [usize; ARG_COUNT]) -> SbiRet {
    let request = SbiCall::new(ext, fid, args);
    let regs = firmware_entry(&request.encode());

    // `a0` holds the error code. A code this implementation does not know
    // is passed through unchanged rather than being folded into "failed":
    // the caller deserves to see what the firmware actually said.
    let error = regs[0] as isize;
    debug_assert!(error == err::SUCCESS || SbiError::from_code(error).is_some());
    SbiRet { error, value: regs[1] }
}

/// Raises a software interrupt on one hart.
///
/// This is the client's entry point for waking another hart.
pub(crate) fn send_ipi(hart: usize) -> SbiRet {
    let Some(mask) = single_hart_mask(hart) else {
        return SbiRet::err(SbiError::InvalidParam);
    };
    call(ext::IPI, fid::IPI_SEND_IPI, [mask, 0, 0, 0, 0, 0])
}

/// Takes back a software interrupt on one hart.
pub(crate) fn clear_ipi(hart: usize) -> SbiRet {
    let Some(mask) = single_hart_mask(hart) else {
        return SbiRet::err(SbiError::InvalidParam);
    };
    call(ext::IPI, fid::IPI_CLEAR_IPI, [mask, 0, 0, 0, 0, 0])
}

/// Writes one character to the debug console.
#[allow(dead_code)]
pub(crate) fn putchar(ch: u8) -> SbiRet {
    call(ext::DBCN, fid::DBCN_PUTCHAR, [ch as usize, 0, 0, 0, 0, 0])
}

/// The mask that selects exactly one hart.
///
/// `None` when the hart does not exist. The check happens here rather than
/// only in the dispatcher because building the mask means shifting by the
/// hart number, and a shift by more than the width of the type is a bug in
/// its own right.
fn single_hart_mask(hart: usize) -> Option<usize> {
    if hart >= NUM_CORES || hart >= usize::BITS as usize {
        return None;
    }
    Some(1usize << hart)
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;
    use core::cell::Cell;

    /// A firmware that records what it was asked to do.
    ///
    /// The dispatch rules are the part of this module that has to be right
    /// for the migration to be safe, and they are worth testing without any
    /// hardware in the picture - the interesting failures are a hart mask
    /// that names a hart that does not exist, an unknown extension being
    /// silently ignored, or the arguments arriving in the wrong registers.
    struct RecordingFirmware {
        timer: Cell<Option<u64>>,
        sent: Cell<usize>,
        cleared: Cell<usize>,
        char: Cell<Option<u8>>,
        char_count: Cell<usize>,
        started_hart: Cell<Option<usize>>,
        reset_type: Cell<Option<u32>>,
        fail_with: Cell<Option<SbiError>>,
    }

    impl RecordingFirmware {
        fn new() -> RecordingFirmware {
            RecordingFirmware {
                timer: Cell::new(None),
                sent: Cell::new(0),
                cleared: Cell::new(0),
                char: Cell::new(None),
                char_count: Cell::new(0),
                started_hart: Cell::new(None),
                reset_type: Cell::new(None),
                fail_with: Cell::new(None),
            }
        }

        fn failing(error: SbiError) -> RecordingFirmware {
            let fw = RecordingFirmware::new();
            fw.fail_with.set(Some(error));
            fw
        }

        fn result(&self) -> Result<(), SbiError> {
            match self.fail_with.get() {
                Some(e) => Err(e),
                None => Ok(()),
            }
        }
    }

    impl Firmware for RecordingFirmware {
        fn set_timer(&mut self, stime_value: u64) -> Result<(), SbiError> {
            self.timer.set(Some(stime_value));
            self.result()
        }

        fn send_ipi(&mut self, hart_mask: usize) -> Result<(), SbiError> {
            self.sent.set(self.sent.get() | hart_mask);
            self.result()
        }

        fn clear_ipi(&mut self, hart_mask: usize) -> Result<(), SbiError> {
            self.cleared.set(self.cleared.get() | hart_mask);
            self.result()
        }

        fn putchar(&mut self, ch: u8) -> Result<(), SbiError> {
            self.char.set(Some(ch));
            self.char_count.set(self.char_count.get() + 1);
            self.result()
        }

        fn hart_start(
            &mut self,
            hart_id: usize,
            _start_addr: u64,
            _opaque: u64,
        ) -> Result<(), SbiError> {
            self.started_hart.set(Some(hart_id));
            self.result()
        }

        fn system_reset(&mut self, reset_type: u32, _reason: u32) -> Result<(), SbiError> {
            self.reset_type.set(Some(reset_type));
            self.result()
        }
    }

    #[test]
    fn call_encoding_round_trips() {
        let request = SbiCall::new(ext::TIME, fid::TIME_SET_TIMER, [11, 22, 33, 44, 55, 66]);
        let regs = request.encode();

        // The specification puts the extension in `a7` and the function in
        // `a6`; the arguments fill `a0`..`a5` in order.
        assert_eq!(regs[7], ext::TIME);
        assert_eq!(regs[6], fid::TIME_SET_TIMER);
        assert_eq!(regs[0], 11);
        assert_eq!(regs[5], 66);

        assert_eq!(SbiCall::decode(regs), request);
    }

    #[test]
    fn unknown_extension_is_reported_not_ignored() {
        let mut fw = RecordingFirmware::new();
        let ret = dispatch(&SbiCall::new(0xdead_beef, 0, [0; ARG_COUNT]), &mut fw);

        assert_eq!(ret.error, err::NOT_SUPPORTED);
        assert!(!ret.is_ok());
        // Nothing may have reached the hardware.
        assert_eq!(fw.sent.get(), 0);
        assert_eq!(fw.timer.get(), None);
    }

    #[test]
    fn unknown_function_is_reported_not_ignored() {
        let mut fw = RecordingFirmware::new();
        let ret = dispatch(&SbiCall::new(ext::TIME, 0x99, [0; ARG_COUNT]), &mut fw);

        assert_eq!(ret.error, err::NOT_SUPPORTED);
        assert_eq!(fw.timer.get(), None);
    }

    #[test]
    fn timer_value_reaches_the_firmware() {
        let mut fw = RecordingFirmware::new();
        let ret = dispatch(
            &SbiCall::new(ext::TIME, fid::TIME_SET_TIMER, [0x1234_5678, 0, 0, 0, 0, 0]),
            &mut fw,
        );

        assert!(ret.is_ok());
        assert_eq!(fw.timer.get(), Some(0x1234_5678));
    }

    #[test]
    fn ipi_mask_reaches_the_firmware() {
        // The mask bits must reach the firmware unchanged. Build masks the
        // platform actually has: a one-hart board (e.g. qemu_riscv32) only
        // accepts bit 0, so the interesting values are "every hart" and
        // "the first hart" - both valid on any NUM_CORES.
        let mut fw = RecordingFirmware::new();
        let ret = dispatch(
            &SbiCall::new(ext::IPI, fid::IPI_SEND_IPI, [HART_MASK, 0, 0, 0, 0, 0]),
            &mut fw,
        );

        assert!(ret.is_ok());
        assert_eq!(fw.sent.get(), HART_MASK);

        let first_hart = HART_MASK & 0b1;
        let mut fw = RecordingFirmware::new();
        let ret = dispatch(
            &SbiCall::new(ext::IPI, fid::IPI_CLEAR_IPI, [first_hart, 0, 0, 0, 0, 0]),
            &mut fw,
        );

        assert!(ret.is_ok());
        assert_eq!(fw.cleared.get(), first_hart);
    }

    #[test]
    fn hart_mask_naming_an_unknown_hart_is_refused() {
        let mut fw = RecordingFirmware::new();
        // A hart that does not exist must not reach the hardware: the
        // implementation turns mask bits into per-hart register writes.
        let bad_mask = 1usize << (NUM_CORES + 1);
        let ret = dispatch(
            &SbiCall::new(ext::IPI, fid::IPI_SEND_IPI, [bad_mask, 0, 0, 0, 0, 0]),
            &mut fw,
        );

        assert_eq!(ret.error, err::INVALID_PARAM);
        assert_eq!(fw.sent.get(), 0);
    }

    #[test]
    fn hart_start_rejects_an_unknown_hart() {
        let mut fw = RecordingFirmware::new();
        let ret = dispatch(
            &SbiCall::new(
                ext::HSM,
                fid::HSM_HART_START,
                [NUM_CORES + 3, 0x8000_0000, 0, 0, 0, 0],
            ),
            &mut fw,
        );

        assert_eq!(ret.error, err::INVALID_PARAM);
        assert_eq!(fw.started_hart.get(), None);
    }

    #[test]
    fn hart_start_passes_its_arguments_through() {
        let mut fw = RecordingFirmware::new();
        let ret = dispatch(
            &SbiCall::new(
                ext::HSM,
                fid::HSM_HART_START,
                [0, 0x8000_0000, 0x1234, 0, 0, 0],
            ),
            &mut fw,
        );

        assert!(ret.is_ok());
        assert_eq!(fw.started_hart.get(), Some(0));
    }

    #[test]
    fn system_reset_rejects_an_unknown_reset_type() {
        let mut fw = RecordingFirmware::new();
        let ret = dispatch(
            &SbiCall::new(ext::SRST, fid::SRST_SYSTEM_RESET, [9, 0, 0, 0, 0, 0]),
            &mut fw,
        );

        assert_eq!(ret.error, err::INVALID_PARAM);
        assert_eq!(fw.reset_type.get(), None);
    }

    #[test]
    fn debug_console_carries_the_character() {
        let mut fw = RecordingFirmware::new();
        let ret = dispatch(
            &SbiCall::new(ext::DBCN, fid::DBCN_PUTCHAR, [b'x' as usize, 0, 0, 0, 0, 0]),
            &mut fw,
        );

        assert!(ret.is_ok());
        assert_eq!(fw.char.get(), Some(b'x'));
        assert_eq!(fw.char_count.get(), 1);
    }

    #[test]
    fn firmware_errors_reach_the_caller() {
        let mut fw = RecordingFirmware::failing(SbiError::Denied);
        let ret = dispatch(
            &SbiCall::new(ext::DBCN, fid::DBCN_PUTCHAR, [b'x' as usize, 0, 0, 0, 0, 0]),
            &mut fw,
        );

        assert_eq!(ret.error, err::DENIED);
        assert_eq!(SbiError::from_code(ret.error), Some(SbiError::Denied));
    }

    #[test]
    fn probing_reports_which_extensions_exist() {
        let mut fw = RecordingFirmware::new();

        let ret = dispatch(
            &SbiCall::new(ext::BASE, fid::BASE_PROBE_EXT, [ext::TIME, 0, 0, 0, 0, 0]),
            &mut fw,
        );
        assert!(ret.is_ok());
        assert_eq!(ret.value, 1);

        let ret = dispatch(
            &SbiCall::new(ext::BASE, fid::BASE_PROBE_EXT, [0xdead_beef, 0, 0, 0, 0, 0]),
            &mut fw,
        );
        assert!(ret.is_ok());
        assert_eq!(ret.value, 0);
    }

    #[test]
    fn a_hart_that_does_not_exist_has_no_mask() {
        // The client has to reject the hart before it builds a mask: a shift
        // by more than the width of the type is undefined behaviour.
        assert_eq!(single_hart_mask(0), Some(1));
        assert_eq!(single_hart_mask(NUM_CORES), None);
        assert_eq!(single_hart_mask(usize::BITS as usize), None);
    }

    #[test]
    fn error_codes_match_the_specification() {
        assert_eq!(SbiError::Failed.code(), -1);
        assert_eq!(SbiError::NotSupported.code(), -2);
        assert_eq!(SbiError::InvalidParam.code(), -3);
        assert_eq!(SbiError::Denied.code(), -4);
        assert_eq!(SbiError::InvalidAddress.code(), -5);

        // The codes are the extension's ASCII spelling, so a register dump
        // of an SBI call is readable.
        assert_eq!(ext::TIME, 0x5449_4d45);
        assert_eq!(ext::IPI, 0x0073_5049);
        assert_eq!(ext::HSM, 0x0048_534d);
        assert_eq!(ext::SRST, 0x5352_5354);
    }

    #[test]
    fn the_firmware_entry_preserves_the_other_registers() {
        // The specification requires every register except `a0` and `a1` to
        // survive the call. The caller may be mid-way through something that
        // depends on them.
        let mut regs = [0usize; REG_COUNT];
        regs[2] = 0x1111_2222;
        regs[5] = 0x3333_4444;
        regs[7] = ext::BASE;
        regs[6] = fid::BASE_GET_SPEC_VERSION;

        let out = firmware_entry(&regs);

        assert_eq!(out[2], 0x1111_2222);
        assert_eq!(out[5], 0x3333_4444);
        // `a0` carries the error code, `a1` the return value.
        assert_eq!(out[0], 0);
        assert_eq!(out[1], 2usize << 24);
    }

    #[test]
    fn the_firmware_entry_reports_an_unknown_extension() {
        let mut regs = [0usize; REG_COUNT];
        regs[7] = 0xdead_beef;

        let out = firmware_entry(&regs);

        assert_eq!(out[0], err::NOT_SUPPORTED as usize);
    }
}
