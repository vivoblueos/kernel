//! SysTick: System Timer

use volatile_register::{RO, RW};

use crate::peripheral::SYST;

/// Register block
#[repr(C)]
pub struct RegisterBlock {
    /// Control and Status
    pub csr: RW<u32>,
    /// Reload Value
    pub rvr: RW<u32>,
    /// Current Value
    pub cvr: RW<u32>,
    /// Calibration Value
    pub calib: RO<u32>,
}

/// SysTick clock source
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SystClkSource {
    /// Core-provided clock
    Core,
    /// External reference clock
    External,
}

const SYST_COUNTER_MASK: u32 = 0x00ff_ffff;

const SYST_CSR_ENABLE: u32 = 1 << 0;
const SYST_CSR_TICKINT: u32 = 1 << 1;
const SYST_CSR_CLKSOURCE: u32 = 1 << 2;
const SYST_CSR_COUNTFLAG: u32 = 1 << 16;

const SYST_CALIB_SKEW: u32 = 1 << 30;
const SYST_CALIB_NOREF: u32 = 1 << 31;

impl SYST {
    /// Clears current value to 0
    ///
    /// After calling `clear_current()`, the next call to `has_wrapped()` will return `false`.
    #[inline]
    pub fn clear_current(&mut self) {
        unsafe { self.cvr.write(0) }
    }

    /// Disables counter
    #[inline]
    pub fn disable_counter(&mut self) {
        unsafe { self.csr.modify(|v| v & !SYST_CSR_ENABLE) }
    }

    /// Disables SysTick interrupt
    #[inline]
    pub fn disable_interrupt(&mut self) {
        unsafe { self.csr.modify(|v| v & !SYST_CSR_TICKINT) }
    }

    /// Enables counter
    ///
    /// *NOTE* The reference manual indicates that:
    ///
    /// "The SysTick counter reload and current value are undefined at reset, the correct
    /// initialization sequence for the SysTick counter is:
    ///
    /// - Program reload value
    /// - Clear current value
    /// - Program Control and Status register"
    ///
    /// The sequence translates to `self.set_reload(x); self.clear_current(); self.enable_counter()`
    #[inline]
    pub fn enable_counter(&mut self) {
        unsafe { self.csr.modify(|v| v | SYST_CSR_ENABLE) }
    }

    /// Enables SysTick interrupt
    #[inline]
    pub fn enable_interrupt(&mut self) {
        unsafe { self.csr.modify(|v| v | SYST_CSR_TICKINT) }
    }

    /// Gets clock source
    ///
    /// *NOTE* This takes `&mut self` because the read operation is side effectful and can clear the
    /// bit that indicates that the timer has wrapped (cf. `SYST.has_wrapped`)
    #[inline]
    pub fn get_clock_source(&mut self) -> SystClkSource {
        // NOTE(unsafe) atomic read with no side effects
        if self.csr.read() & SYST_CSR_CLKSOURCE != 0 {
            SystClkSource::Core
        } else {
            SystClkSource::External
        }
    }

    /// Gets current value
    #[inline]
    pub fn get_current() -> u32 {
        // NOTE(unsafe) atomic read with no side effects
        unsafe { (*Self::PTR).cvr.read() }
    }

    /// Gets reload value
    #[inline]
    pub fn get_reload() -> u32 {
        // NOTE(unsafe) atomic read with no side effects
        unsafe { (*Self::PTR).rvr.read() }
    }

    /// Returns the reload value with which the counter would wrap once per 10
    /// ms
    ///
    /// Returns `0` if the value is not known (e.g. because the clock can
    /// change dynamically).
    #[inline]
    pub fn get_ticks_per_10ms() -> u32 {
        // NOTE(unsafe) atomic read with no side effects
        unsafe { (*Self::PTR).calib.read() & SYST_COUNTER_MASK }
    }

    /// Checks if an external reference clock is available
    #[inline]
    pub fn has_reference_clock() -> bool {
        // NOTE(unsafe) atomic read with no side effects
        unsafe { (*Self::PTR).calib.read() & SYST_CALIB_NOREF == 0 }
    }

    /// Checks if the counter wrapped (underflowed) since the last check
    ///
    /// *NOTE* This takes `&mut self` because the read operation is side effectful and will clear
    /// the bit of the read register.
    #[inline]
    pub fn has_wrapped(&mut self) -> bool {
        self.csr.read() & SYST_CSR_COUNTFLAG != 0
    }

    /// Checks if counter is enabled
    ///
    /// *NOTE* This takes `&mut self` because the read operation is side effectful and can clear the
    /// bit that indicates that the timer has wrapped (cf. `SYST.has_wrapped`)
    #[inline]
    pub fn is_counter_enabled(&mut self) -> bool {
        self.csr.read() & SYST_CSR_ENABLE != 0
    }

    /// Checks if SysTick interrupt is enabled
    ///
    /// *NOTE* This takes `&mut self` because the read operation is side effectful and can clear the
    /// bit that indicates that the timer has wrapped (cf. `SYST.has_wrapped`)
    #[inline]
    pub fn is_interrupt_enabled(&mut self) -> bool {
        self.csr.read() & SYST_CSR_TICKINT != 0
    }

    /// Checks if the calibration value is precise
    ///
    /// Returns `false` if using the reload value returned by
    /// `get_ticks_per_10ms()` may result in a period significantly deviating
    /// from 10 ms.
    #[inline]
    pub fn is_precise() -> bool {
        // NOTE(unsafe) atomic read with no side effects
        unsafe { (*Self::PTR).calib.read() & SYST_CALIB_SKEW == 0 }
    }

    /// Sets clock source
    #[inline]
    pub fn set_clock_source(&mut self, clk_source: SystClkSource) {
        match clk_source {
            SystClkSource::External => unsafe { self.csr.modify(|v| v & !SYST_CSR_CLKSOURCE) },
            SystClkSource::Core => unsafe { self.csr.modify(|v| v | SYST_CSR_CLKSOURCE) },
        }
    }

    /// Sets reload value
    ///
    /// Valid values are between `1` and `0x00ffffff`.
    ///
    /// *NOTE* To make the timer wrap every `N` ticks set the reload value to `N - 1`
    #[inline]
    pub fn set_reload(&mut self, value: u32) {
        unsafe { self.rvr.write(value) }
    }
}
