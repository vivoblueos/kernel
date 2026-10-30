//! Instrumentation Trace Macrocell
//!
//! *NOTE* Not available on Armv6-M and Armv8-M Baseline.

use core::cell::UnsafeCell;
use core::ptr;

use volatile_register::{RO, RW, WO};

/// Register block
#[repr(C)]
pub struct RegisterBlock {
    /// Stimulus Port
    pub stim: [Stim; 256],
    reserved0: [u32; 640],
    /// Trace Enable
    pub ter: [RW<u32>; 8],
    reserved1: [u32; 8],
    /// Trace Privilege
    pub tpr: RW<u32>,
    reserved2: [u32; 15],
    /// Trace Control
    pub tcr: RW<u32>,
    reserved3: [u32; 75],
    /// Lock Access
    pub lar: WO<u32>,
    /// Lock Status
    pub lsr: RO<u32>,
}

/// Stimulus Port
pub struct Stim {
    register: UnsafeCell<u32>,
}

impl Stim {
    /// Writes an `u8` payload into the stimulus port
    #[inline]
    pub fn write_u8(&mut self, value: u8) {
        unsafe { ptr::write_volatile(self.register.get() as *mut u8, value) }
    }

    /// Writes an `u16` payload into the stimulus port
    #[inline]
    pub fn write_u16(&mut self, value: u16) {
        unsafe { ptr::write_volatile(self.register.get() as *mut u16, value) }
    }

    /// Writes an `u32` payload into the stimulus port
    #[inline]
    pub fn write_u32(&mut self, value: u32) {
        unsafe { ptr::write_volatile(self.register.get(), value) }
    }

    /// Returns `true` if the stimulus port is ready to accept more data
    #[cfg(not(armv8m))]
    #[inline]
    pub fn is_fifo_ready(&self) -> bool {
        unsafe { ptr::read_volatile(self.register.get()) & 0b1 == 1 }
    }

    /// Returns `true` if the stimulus port is ready to accept more data
    #[cfg(armv8m)]
    #[inline]
    pub fn is_fifo_ready(&self) -> bool {
        // ARMv8-M adds a disabled bit; we indicate that we are ready to
        // proceed with a stimulus write if the port is either ready (bit 0) or
        // disabled (bit 1).
        unsafe { ptr::read_volatile(self.register.get()) & 0b11 != 0 }
    }
}
