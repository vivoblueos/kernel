// Copyright 2025 The safe-mmio Authors.
// This project is dual-licensed under Apache 2.0 and MIT terms.
// See LICENSE-APACHE and LICENSE-MIT for details.

use crate::{SharedMmioPointer, UniqueMmioPointer};

impl<T> UniqueMmioPointer<'_, T> {
    /// Performs an MMIO read of the entire `T`.
    ///
    /// # Safety
    ///
    /// This field must be safe to perform an MMIO read from.
    pub unsafe fn read_unsafe(&mut self) -> T {
        // SAFETY: self.regs is always a valid and unique pointer to MMIO address space.
        unsafe { self.regs.read_volatile() }
    }

    /// Performs an MMIO write of the entire `T`.
    ///
    /// Note that this takes `&mut self` rather than `&self` because an MMIO read may cause
    /// side-effects that change the state of the device.
    ///
    /// # Safety
    ///
    /// This field must be safe to perform an MMIO write to.
    pub unsafe fn write_unsafe(&mut self, value: T) {
        // SAFETY: self.regs is always a valid and unique pointer to MMIO address space.
        unsafe {
            self.regs.write_volatile(value);
        }
    }
}

impl<T> SharedMmioPointer<'_, T> {
    /// Performs an MMIO read of the entire `T`.
    ///
    /// # Safety
    ///
    /// This field must be safe to perform an MMIO read from, and doing so must not cause any
    /// side-effects.
    pub unsafe fn read_unsafe(&self) -> T {
        // SAFETY: self.regs is always a valid and unique pointer to MMIO address space.
        unsafe { self.regs.read_volatile() }
    }
}
