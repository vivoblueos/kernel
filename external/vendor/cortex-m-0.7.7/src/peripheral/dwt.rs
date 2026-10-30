//! Data Watchpoint and Trace unit

#[cfg(not(armv6m))]
use volatile_register::WO;
use volatile_register::{RO, RW};

use crate::peripheral::DWT;

/// Register block
#[repr(C)]
pub struct RegisterBlock {
    /// Control
    pub ctrl: RW<u32>,
    /// Cycle Count
    #[cfg(not(armv6m))]
    pub cyccnt: RW<u32>,
    /// CPI Count
    #[cfg(not(armv6m))]
    pub cpicnt: RW<u32>,
    /// Exception Overhead Count
    #[cfg(not(armv6m))]
    pub exccnt: RW<u32>,
    /// Sleep Count
    #[cfg(not(armv6m))]
    pub sleepcnt: RW<u32>,
    /// LSU Count
    #[cfg(not(armv6m))]
    pub lsucnt: RW<u32>,
    /// Folded-instruction Count
    #[cfg(not(armv6m))]
    pub foldcnt: RW<u32>,
    /// Cortex-M0(+) does not have  these parts
    #[cfg(armv6m)]
    reserved: [u32; 6],
    /// Program Counter Sample
    pub pcsr: RO<u32>,
    /// Comparators
    #[cfg(armv6m)]
    pub c: [Comparator; 2],
    #[cfg(not(armv6m))]
    /// Comparators
    pub c: [Comparator; 16],
    #[cfg(not(armv6m))]
    reserved: [u32; 932],
    /// Lock Access
    #[cfg(not(armv6m))]
    pub lar: WO<u32>,
    /// Lock Status
    #[cfg(not(armv6m))]
    pub lsr: RO<u32>,
}

/// Comparator
#[repr(C)]
pub struct Comparator {
    /// Comparator
    pub comp: RW<u32>,
    /// Comparator Mask
    pub mask: RW<u32>,
    /// Comparator Function
    pub function: RW<u32>,
    reserved: u32,
}

// DWT CTRL register fields
const NUMCOMP_OFFSET: u32 = 28;
const NOTRCPKT: u32 = 1 << 27;
const NOEXTTRIG: u32 = 1 << 26;
const NOCYCCNT: u32 = 1 << 25;
const NOPRFCNT: u32 = 1 << 24;
const CYCCNTENA: u32 = 1 << 0;

impl DWT {
    /// Number of comparators implemented
    ///
    /// A value of zero indicates no comparator support.
    #[inline]
    pub fn num_comp() -> u8 {
        // NOTE(unsafe) atomic read with no side effects
        unsafe { ((*Self::PTR).ctrl.read() >> NUMCOMP_OFFSET) as u8 }
    }

    /// Returns `true` if the the implementation supports sampling and exception tracing
    #[cfg(not(armv6m))]
    #[inline]
    pub fn has_exception_trace() -> bool {
        // NOTE(unsafe) atomic read with no side effects
        unsafe { (*Self::PTR).ctrl.read() & NOTRCPKT == 0 }
    }

    /// Returns `true` if the implementation includes external match signals
    #[cfg(not(armv6m))]
    #[inline]
    pub fn has_external_match() -> bool {
        // NOTE(unsafe) atomic read with no side effects
        unsafe { (*Self::PTR).ctrl.read() & NOEXTTRIG == 0 }
    }

    /// Returns `true` if the implementation supports a cycle counter
    #[cfg(not(armv6m))]
    #[inline]
    pub fn has_cycle_counter() -> bool {
        // NOTE(unsafe) atomic read with no side effects
        unsafe { (*Self::PTR).ctrl.read() & NOCYCCNT == 0 }
    }

    /// Returns `true` if the implementation the profiling counters
    #[cfg(not(armv6m))]
    #[inline]
    pub fn has_profiling_counter() -> bool {
        // NOTE(unsafe) atomic read with no side effects
        unsafe { (*Self::PTR).ctrl.read() & NOPRFCNT == 0 }
    }

    /// Enables the cycle counter
    ///
    /// The global trace enable ([`DCB::enable_trace`]) should be set before
    /// enabling the cycle counter, the processor may ignore writes to the
    /// cycle counter enable if the global trace is disabled
    /// (implementation defined behaviour).
    ///
    /// [`DCB::enable_trace`]: crate::peripheral::DCB::enable_trace
    #[cfg(not(armv6m))]
    #[inline]
    pub fn enable_cycle_counter(&mut self) {
        unsafe { self.ctrl.modify(|r| r | CYCCNTENA) }
    }

    /// Disables the cycle counter
    #[cfg(not(armv6m))]
    #[inline]
    pub fn disable_cycle_counter(&mut self) {
        unsafe { self.ctrl.modify(|r| r & !CYCCNTENA) }
    }

    /// Returns `true` if the cycle counter is enabled
    #[cfg(not(armv6m))]
    #[inline]
    pub fn cycle_counter_enabled() -> bool {
        // NOTE(unsafe) atomic read with no side effects
        unsafe { (*Self::PTR).ctrl.read() & CYCCNTENA != 0 }
    }

    /// Returns the current clock cycle count
    #[cfg(not(armv6m))]
    #[inline]
    #[deprecated(
        since = "0.7.4",
        note = "Use `cycle_count` which follows the C-GETTER convention"
    )]
    pub fn get_cycle_count() -> u32 {
        Self::cycle_count()
    }

    /// Returns the current clock cycle count
    #[cfg(not(armv6m))]
    #[inline]
    pub fn cycle_count() -> u32 {
        // NOTE(unsafe) atomic read with no side effects
        unsafe { (*Self::PTR).cyccnt.read() }
    }

    /// Set the cycle count
    #[cfg(not(armv6m))]
    #[inline]
    pub fn set_cycle_count(&mut self, count: u32) {
        unsafe { self.cyccnt.write(count) }
    }

    /// Removes the software lock on the DWT
    ///
    /// Some devices, like the STM32F7, software lock the DWT after a power cycle.
    #[cfg(not(armv6m))]
    #[inline]
    pub fn unlock() {
        // NOTE(unsafe) atomic write to a stateless, write-only register
        unsafe { (*Self::PTR).lar.write(0xC5AC_CE55) }
    }

    /// Get the CPI count
    ///
    /// Counts additional cycles required to execute multi-cycle instructions,
    /// except those recorded by [`lsu_count`], and counts any instruction fetch
    /// stalls.
    ///
    /// [`lsu_count`]: DWT::lsu_count
    #[cfg(not(armv6m))]
    #[inline]
    pub fn cpi_count() -> u8 {
        // NOTE(unsafe) atomic read with no side effects
        unsafe { (*Self::PTR).cpicnt.read() as u8 }
    }

    /// Set the CPI count
    #[cfg(not(armv6m))]
    #[inline]
    pub fn set_cpi_count(&mut self, count: u8) {
        unsafe { self.cpicnt.write(count as u32) }
    }

    /// Get the total cycles spent in exception processing
    #[cfg(not(armv6m))]
    #[inline]
    pub fn exception_count() -> u8 {
        // NOTE(unsafe) atomic read with no side effects
        unsafe { (*Self::PTR).exccnt.read() as u8 }
    }

    /// Set the exception count
    #[cfg(not(armv6m))]
    #[inline]
    pub fn set_exception_count(&mut self, count: u8) {
        unsafe { self.exccnt.write(count as u32) }
    }

    /// Get the total number of cycles that the processor is sleeping
    ///
    /// ARM recommends that this counter counts all cycles when the processor is sleeping,
    /// regardless of whether a WFI or WFE instruction, or the sleep-on-exit functionality,
    /// caused the entry to sleep mode.
    /// However, all sleep features are implementation defined and therefore when
    /// this counter counts is implementation defined.
    #[cfg(not(armv6m))]
    #[inline]
    pub fn sleep_count() -> u8 {
        // NOTE(unsafe) atomic read with no side effects
        unsafe { (*Self::PTR).sleepcnt.read() as u8 }
    }

    /// Set the sleep count
    #[cfg(not(armv6m))]
    #[inline]
    pub fn set_sleep_count(&mut self, count: u8) {
        unsafe { self.sleepcnt.write(count as u32) }
    }

    /// Get the additional cycles required to execute all load or store instructions
    #[cfg(not(armv6m))]
    #[inline]
    pub fn lsu_count() -> u8 {
        // NOTE(unsafe) atomic read with no side effects
        unsafe { (*Self::PTR).lsucnt.read() as u8 }
    }

    /// Set the lsu count
    #[cfg(not(armv6m))]
    #[inline]
    pub fn set_lsu_count(&mut self, count: u8) {
        unsafe { self.lsucnt.write(count as u32) }
    }

    /// Get the folded instruction count
    ///
    /// Increments on each instruction that takes 0 cycles.
    #[cfg(not(armv6m))]
    #[inline]
    pub fn fold_count() -> u8 {
        // NOTE(unsafe) atomic read with no side effects
        unsafe { (*Self::PTR).foldcnt.read() as u8 }
    }

    /// Set the folded instruction count
    #[cfg(not(armv6m))]
    #[inline]
    pub fn set_fold_count(&mut self, count: u8) {
        unsafe { self.foldcnt.write(count as u32) }
    }
}
