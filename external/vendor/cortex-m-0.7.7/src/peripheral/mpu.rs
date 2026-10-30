//! Memory Protection Unit

use volatile_register::{RO, RW};

/// Register block for ARMv7-M
#[cfg(not(armv8m))]
#[repr(C)]
pub struct RegisterBlock {
    /// Type
    pub _type: RO<u32>,
    /// Control
    pub ctrl: RW<u32>,
    /// Region Number
    pub rnr: RW<u32>,
    /// Region Base Address
    pub rbar: RW<u32>,
    /// Region Attribute and Size
    pub rasr: RW<u32>,
    /// Alias 1 of RBAR
    pub rbar_a1: RW<u32>,
    /// Alias 1 of RASR
    pub rasr_a1: RW<u32>,
    /// Alias 2 of RBAR
    pub rbar_a2: RW<u32>,
    /// Alias 2 of RASR
    pub rasr_a2: RW<u32>,
    /// Alias 3 of RBAR
    pub rbar_a3: RW<u32>,
    /// Alias 3 of RASR
    pub rasr_a3: RW<u32>,
}

/// Register block for ARMv8-M
#[cfg(armv8m)]
#[repr(C)]
pub struct RegisterBlock {
    /// Type
    pub _type: RO<u32>,
    /// Control
    pub ctrl: RW<u32>,
    /// Region Number
    pub rnr: RW<u32>,
    /// Region Base Address
    pub rbar: RW<u32>,
    /// Region Limit Address
    pub rlar: RW<u32>,
    /// Alias 1 of RBAR
    pub rbar_a1: RW<u32>,
    /// Alias 1 of RLAR
    pub rlar_a1: RW<u32>,
    /// Alias 2 of RBAR
    pub rbar_a2: RW<u32>,
    /// Alias 2 of RLAR
    pub rlar_a2: RW<u32>,
    /// Alias 3 of RBAR
    pub rbar_a3: RW<u32>,
    /// Alias 3 of RLAR
    pub rlar_a3: RW<u32>,

    // Reserved word at offset 0xBC
    _reserved: u32,

    /// Memory Attribute Indirection register 0 and 1
    pub mair: [RW<u32>; 2],
}
