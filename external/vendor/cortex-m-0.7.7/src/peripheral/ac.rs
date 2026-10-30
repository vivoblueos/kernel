//! Cortex-M7 TCM and Cache access control.

use volatile_register::RW;

/// Register block
#[repr(C)]
pub struct RegisterBlock {
    /// Instruction Tightly-Coupled Memory Control Register
    pub itcmcr: RW<u32>,
    /// Data Tightly-Coupled Memory Control Register
    pub dtcmcr: RW<u32>,
    /// AHBP Control Register
    pub ahbpcr: RW<u32>,
    /// L1 Cache Control Register
    pub cacr: RW<u32>,
    /// AHB Slave Control Register
    pub ahbscr: RW<u32>,
    reserved0: u32,
    /// Auxilary Bus Fault Status Register
    pub abfsr: RW<u32>,
}

/// ITCMCR and DTCMCR TCM enable bit.
pub const TCM_EN: u32 = 1;

/// ITCMCR and DTCMCR TCM read-modify-write bit.
pub const TCM_RMW: u32 = 2;

/// ITCMCR and DTCMCR TCM rety phase enable bit.
pub const TCM_RETEN: u32 = 4;

/// ITCMCR and DTCMCR TCM size mask.
pub const TCM_SZ_MASK: u32 = 0x78;

/// ITCMCR and DTCMCR TCM shift.
pub const TCM_SZ_SHIFT: usize = 3;

/// AHBPCR AHBP enable bit.
pub const AHBPCR_EN: u32 = 1;

/// AHBPCR AHBP size mask.
pub const AHBPCR_SZ_MASK: u32 = 0x0e;

/// AHBPCR AHBP size shit.
pub const AHBPCR_SZ_SHIFT: usize = 1;

/// CACR Shared cachedable-is-WT for data cache.
pub const CACR_SIWT: u32 = 1;

/// CACR ECC in the instruction and data cache (disable).
pub const CACR_ECCDIS: u32 = 2;

/// CACR Force Write-Through in the data cache.
pub const CACR_FORCEWT: u32 = 4;

/// AHBSCR AHBS prioritization control mask.
pub const AHBSCR_CTL_MASK: u32 = 0x03;

/// AHBSCR AHBS prioritization control shift.
pub const AHBSCR_CTL_SHIFT: usize = 0;

/// AHBSCR Threshold execution prioity for AHBS traffic demotion, mask.
pub const AHBSCR_TPRI_MASK: u32 = 0x7fc;

/// AHBSCR Threshold execution prioity for AHBS traffic demotion, shift.
pub const AHBSCR_TPRI_SHIFT: usize = 2;

/// AHBSCR Failness counter initialization value, mask.
pub const AHBSCR_INITCOUNT_MASK: u32 = 0xf800;

/// AHBSCR Failness counter initialization value, shift.
pub const AHBSCR_INITCOUNT_SHIFT: usize = 11;

/// ABFSR Async fault on ITCM interface.
pub const ABFSR_ITCM: u32 = 1;

/// ABFSR Async fault on DTCM interface.
pub const ABFSR_DTCM: u32 = 2;

/// ABFSR Async fault on AHBP interface.
pub const ABFSR_AHBP: u32 = 4;

/// ABFSR Async fault on AXIM interface.
pub const ABFSR_AXIM: u32 = 8;

/// ABFSR Async fault on EPPB interface.
pub const ABFSR_EPPB: u32 = 16;

/// ABFSR Indicates the type of fault on the AXIM interface, mask.
pub const ABFSR_AXIMTYPE_MASK: u32 = 0x300;

/// ABFSR Indicates the type of fault on the AXIM interface, shift.
pub const ABFSR_AXIMTYPE_SHIFT: usize = 8;
