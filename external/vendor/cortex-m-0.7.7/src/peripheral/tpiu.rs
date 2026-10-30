//! Trace Port Interface Unit;
//!
//! *NOTE* Not available on Armv6-M.

use volatile_register::{RO, RW, WO};

/// Register block
#[repr(C)]
pub struct RegisterBlock {
    /// Supported Parallel Port Sizes
    pub sspsr: RO<u32>,
    /// Current Parallel Port Size
    pub cspsr: RW<u32>,
    reserved0: [u32; 2],
    /// Asynchronous Clock Prescaler
    pub acpr: RW<u32>,
    reserved1: [u32; 55],
    /// Selected Pin Control
    pub sppr: RW<u32>,
    reserved2: [u32; 132],
    /// Formatter and Flush Control
    pub ffcr: RW<u32>,
    reserved3: [u32; 810],
    /// Lock Access
    pub lar: WO<u32>,
    /// Lock Status
    pub lsr: RO<u32>,
    reserved4: [u32; 4],
    /// TPIU Type
    pub _type: RO<u32>,
}
