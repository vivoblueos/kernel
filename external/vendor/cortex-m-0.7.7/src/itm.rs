//! Instrumentation Trace Macrocell
//!
//! **NOTE** This module is only available on ARMv7-M and newer.

use core::{fmt, ptr, slice};

use crate::peripheral::itm::Stim;

// NOTE assumes that `bytes` is 32-bit aligned
unsafe fn write_words(stim: &mut Stim, bytes: &[u32]) {
    let mut p = bytes.as_ptr();
    for _ in 0..bytes.len() {
        while !stim.is_fifo_ready() {}
        stim.write_u32(ptr::read(p));
        p = p.offset(1);
    }
}

/// Writes an aligned byte slice to the ITM.
///
/// `buffer` must be 4-byte aligned.
unsafe fn write_aligned_impl(port: &mut Stim, buffer: &[u8]) {
    let len = buffer.len();

    if len == 0 {
        return;
    }

    let split = len & !0b11;
    #[allow(clippy::cast_ptr_alignment)]
    write_words(
        port,
        slice::from_raw_parts(buffer.as_ptr() as *const u32, split >> 2),
    );

    // 3 bytes or less left
    let mut left = len & 0b11;
    let mut ptr = buffer.as_ptr().add(split);

    // at least 2 bytes left
    if left > 1 {
        while !port.is_fifo_ready() {}

        #[allow(clippy::cast_ptr_alignment)]
        port.write_u16(ptr::read(ptr as *const u16));

        ptr = ptr.offset(2);
        left -= 2;
    }

    // final byte
    if left == 1 {
        while !port.is_fifo_ready() {}
        port.write_u8(*ptr);
    }
}

struct Port<'p>(&'p mut Stim);

impl<'p> fmt::Write for Port<'p> {
    #[inline]
    fn write_str(&mut self, s: &str) -> fmt::Result {
        write_all(self.0, s.as_bytes());
        Ok(())
    }
}

/// A wrapper type that aligns its contents on a 4-Byte boundary.
///
/// ITM transfers are most efficient when the data is 4-Byte-aligned. This type provides an easy
/// way to accomplish and enforce such an alignment.
#[repr(align(4))]
pub struct Aligned<T: ?Sized>(pub T);

/// Writes `buffer` to an ITM port.
#[allow(clippy::missing_inline_in_public_items)]
pub fn write_all(port: &mut Stim, buffer: &[u8]) {
    unsafe {
        let mut len = buffer.len();
        let mut ptr = buffer.as_ptr();

        if len == 0 {
            return;
        }

        // 0x01 OR 0x03
        if ptr as usize % 2 == 1 {
            while !port.is_fifo_ready() {}
            port.write_u8(*ptr);

            // 0x02 OR 0x04
            ptr = ptr.offset(1);
            len -= 1;
        }

        // 0x02
        if ptr as usize % 4 == 2 {
            if len > 1 {
                // at least 2 bytes
                while !port.is_fifo_ready() {}

                // We checked the alignment above, so this is safe
                #[allow(clippy::cast_ptr_alignment)]
                port.write_u16(ptr::read(ptr as *const u16));

                // 0x04
                ptr = ptr.offset(2);
                len -= 2;
            } else {
                if len == 1 {
                    // last byte
                    while !port.is_fifo_ready() {}
                    port.write_u8(*ptr);
                }

                return;
            }
        }

        // The remaining data is 4-byte aligned, but might not be a multiple of 4 bytes
        write_aligned_impl(port, slice::from_raw_parts(ptr, len));
    }
}

/// Writes a 4-byte aligned `buffer` to an ITM port.
///
/// # Examples
///
/// ```no_run
/// # use cortex_m::{itm::{self, Aligned}, peripheral::ITM};
/// # let port = unsafe { &mut (*ITM::PTR).stim[0] };
/// let mut buffer = Aligned([0; 14]);
///
/// buffer.0.copy_from_slice(b"Hello, world!\n");
///
/// itm::write_aligned(port, &buffer);
///
/// // Or equivalently
/// itm::write_aligned(port, &Aligned(*b"Hello, world!\n"));
/// ```
#[allow(clippy::missing_inline_in_public_items)]
pub fn write_aligned(port: &mut Stim, buffer: &Aligned<[u8]>) {
    unsafe { write_aligned_impl(port, &buffer.0) }
}

/// Writes `fmt::Arguments` to the ITM `port`
#[inline]
pub fn write_fmt(port: &mut Stim, args: fmt::Arguments) {
    use core::fmt::Write;

    Port(port).write_fmt(args).ok();
}

/// Writes a string to the ITM `port`
#[inline]
pub fn write_str(port: &mut Stim, string: &str) {
    write_all(port, string.as_bytes())
}
