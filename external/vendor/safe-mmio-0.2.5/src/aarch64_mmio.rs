// Copyright 2025 The safe-mmio Authors.
// This project is dual-licensed under Apache 2.0 and MIT terms.
// See LICENSE-APACHE and LICENSE-MIT for details.

use crate::{SharedMmioPointer, UniqueMmioPointer};
use core::ptr::NonNull;
use zerocopy::{FromBytes, Immutable, IntoBytes};

macro_rules! asm_mmio {
    ($t:ty, $read_name:ident, $read_assembly:literal, $write_name:ident, $write_assembly:literal) => {
        unsafe fn $read_name(ptr: *const $t) -> $t {
            let value;
            unsafe {
                core::arch::asm!(
                    $read_assembly,
                    value = out(reg) value,
                    ptr = in(reg) ptr,
                );
            }
            value
        }

        unsafe fn $write_name(ptr: *mut $t, value: $t) {
            unsafe {
                core::arch::asm!(
                    $write_assembly,
                    value = in(reg) value,
                    ptr = in(reg) ptr,
                );
            }
        }
    };
}

asm_mmio!(
    u8,
    read_u8,
    "ldrb {value:w}, [{ptr}]",
    write_u8,
    "strb {value:w}, [{ptr}]"
);
asm_mmio!(
    u16,
    read_u16,
    "ldrh {value:w}, [{ptr}]",
    write_u16,
    "strh {value:w}, [{ptr}]"
);
asm_mmio!(
    u32,
    read_u32,
    "ldr {value:w}, [{ptr}]",
    write_u32,
    "str {value:w}, [{ptr}]"
);
asm_mmio!(
    u64,
    read_u64,
    "ldr {value:x}, [{ptr}]",
    write_u64,
    "str {value:x}, [{ptr}]"
);

impl<T: FromBytes + IntoBytes> UniqueMmioPointer<'_, T> {
    /// Performs an MMIO read and returns the value.
    ///
    /// If `T` is exactly 1, 2, 4 or 8 bytes long then this will be a single operation. Otherwise
    /// it will be split into several, reading chunks as large as possible.
    ///
    /// Note that this takes `&mut self` rather than `&self` because an MMIO read may cause
    /// side-effects that change the state of the device.
    ///
    /// # Safety
    ///
    /// This field must be safe to perform an MMIO read from.
    pub unsafe fn read_unsafe(&mut self) -> T {
        unsafe { mmio_read(self.regs) }
    }
}

impl<T: Immutable + IntoBytes> UniqueMmioPointer<'_, T> {
    /// Performs an MMIO write of the given value.
    ///
    /// If `T` is exactly 1, 2, 4 or 8 bytes long then this will be a single operation. Otherwise
    /// it will be split into several, writing chunks as large as possible.
    ///
    /// # Safety
    ///
    /// This field must be safe to perform an MMIO write to.
    pub unsafe fn write_unsafe(&self, value: T) {
        match size_of::<T>() {
            1 => unsafe { write_u8(self.regs.cast().as_ptr(), value.as_bytes()[0]) },
            2 => unsafe { write_u16(self.regs.cast().as_ptr(), convert(value)) },
            4 => unsafe { write_u32(self.regs.cast().as_ptr(), convert(value)) },
            8 => unsafe { write_u64(self.regs.cast().as_ptr(), convert(value)) },
            _ => unsafe { write_slice(self.regs.cast(), value.as_bytes()) },
        }
    }
}

impl<T: FromBytes + IntoBytes> SharedMmioPointer<'_, T> {
    /// Performs an MMIO read and returns the value.
    ///
    /// If `T` is exactly 1, 2, 4 or 8 bytes long then this will be a single operation. Otherwise
    /// it will be split into several, reading chunks as large as possible.
    ///
    /// # Safety
    ///
    /// This field must be safe to perform an MMIO read from, and doing so must not cause any
    /// side-effects.
    pub unsafe fn read_unsafe(&self) -> T {
        unsafe { mmio_read(self.regs) }
    }
}

/// Performs an MMIO read and returns the value.
///
/// # Safety
///
/// The pointer must be valid to perform an MMIO read from.
unsafe fn mmio_read<T: FromBytes + IntoBytes>(ptr: NonNull<T>) -> T {
    match size_of::<T>() {
        1 => convert(unsafe { read_u8(ptr.cast().as_ptr()) }),
        2 => convert(unsafe { read_u16(ptr.cast().as_ptr()) }),
        4 => convert(unsafe { read_u32(ptr.cast().as_ptr()) }),
        8 => convert(unsafe { read_u64(ptr.cast().as_ptr()) }),
        _ => {
            let mut value = T::new_zeroed();
            unsafe { read_slice(ptr.cast(), value.as_mut_bytes()) };
            value
        }
    }
}

fn convert<T: Immutable + IntoBytes, U: FromBytes>(value: T) -> U {
    U::read_from_bytes(value.as_bytes()).unwrap()
}

unsafe fn write_slice(ptr: NonNull<u8>, slice: &[u8]) {
    if let Some((first, rest)) = slice.split_at_checked(8) {
        unsafe {
            write_u64(ptr.cast().as_ptr(), u64::read_from_bytes(first).unwrap());
            write_slice(ptr.add(8), rest);
        }
    } else if let Some((first, rest)) = slice.split_at_checked(4) {
        unsafe {
            write_u32(ptr.cast().as_ptr(), u32::read_from_bytes(first).unwrap());
            write_slice(ptr.add(4), rest);
        }
    } else if let Some((first, rest)) = slice.split_at_checked(2) {
        unsafe {
            write_u16(ptr.cast().as_ptr(), u16::read_from_bytes(first).unwrap());
            write_slice(ptr.add(2), rest);
        }
    } else if let [first, rest @ ..] = slice {
        unsafe {
            write_u8(ptr.as_ptr(), *first);
            write_slice(ptr.add(1), rest);
        }
    }
}

unsafe fn read_slice(ptr: NonNull<u8>, slice: &mut [u8]) {
    if let Some((first, rest)) = slice.split_at_mut_checked(8) {
        unsafe {
            read_u64(ptr.cast().as_ptr()).write_to(first).unwrap();
            read_slice(ptr.add(8), rest);
        }
    } else if let Some((first, rest)) = slice.split_at_mut_checked(4) {
        unsafe {
            read_u32(ptr.cast().as_ptr()).write_to(first).unwrap();
            read_slice(ptr.add(4), rest);
        }
    } else if let Some((first, rest)) = slice.split_at_mut_checked(2) {
        unsafe {
            read_u16(ptr.cast().as_ptr()).write_to(first).unwrap();
            read_slice(ptr.add(2), rest);
        }
    } else if let [first, rest @ ..] = slice {
        unsafe {
            *first = read_u8(ptr.as_ptr());
            read_slice(ptr.add(1), rest);
        }
    }
}
