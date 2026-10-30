//! Flash Patch and Breakpoint unit
//!
//! *NOTE* Not available on Armv6-M.

use volatile_register::{RO, RW, WO};

/// Register block
#[repr(C)]
pub struct RegisterBlock {
    /// Control
    pub ctrl: RW<u32>,
    /// Remap
    pub remap: RW<u32>,
    /// Comparator
    pub comp: [RW<u32>; 127],
    reserved: [u32; 875],
    /// Lock Access
    pub lar: WO<u32>,
    /// Lock Status
    pub lsr: RO<u32>,
}
