//! A delay driver based on SysTick.

use crate::peripheral::{syst::SystClkSource, SYST};
use embedded_hal::blocking::delay::{DelayMs, DelayUs};

/// System timer (SysTick) as a delay provider.
pub struct Delay {
    syst: SYST,
    frequency: u32,
}

impl Delay {
    /// Configures the system timer (SysTick) as a delay provider.
    ///
    /// `ahb_frequency` is a frequency of the AHB bus in Hz.
    #[inline]
    pub fn new(syst: SYST, ahb_frequency: u32) -> Self {
        Self::with_source(syst, ahb_frequency, SystClkSource::Core)
    }

    /// Configures the system timer (SysTick) as a delay provider
    /// with a clock source.
    ///
    /// `frequency` is the frequency of your `clock_source` in Hz.
    #[inline]
    pub fn with_source(mut syst: SYST, frequency: u32, clock_source: SystClkSource) -> Self {
        syst.set_clock_source(clock_source);

        Delay { syst, frequency }
    }

    /// Releases the system timer (SysTick) resource.
    #[inline]
    pub fn free(self) -> SYST {
        self.syst
    }

    /// Delay using the Cortex-M systick for a certain duration, in µs.
    #[allow(clippy::missing_inline_in_public_items)]
    pub fn delay_us(&mut self, us: u32) {
        let ticks = (u64::from(us)) * (u64::from(self.frequency)) / 1_000_000;

        let full_cycles = ticks >> 24;
        if full_cycles > 0 {
            self.syst.set_reload(0xffffff);
            self.syst.clear_current();
            self.syst.enable_counter();

            for _ in 0..full_cycles {
                while !self.syst.has_wrapped() {}
            }
        }

        let ticks = (ticks & 0xffffff) as u32;
        if ticks > 1 {
            self.syst.set_reload(ticks - 1);
            self.syst.clear_current();
            self.syst.enable_counter();

            while !self.syst.has_wrapped() {}
        }

        self.syst.disable_counter();
    }

    /// Delay using the Cortex-M systick for a certain duration, in ms.
    #[inline]
    pub fn delay_ms(&mut self, mut ms: u32) {
        // 4294967 is the highest u32 value which you can multiply by 1000 without overflow
        while ms > 4294967 {
            self.delay_us(4294967000u32);
            ms -= 4294967;
        }
        self.delay_us(ms * 1_000);
    }
}

impl DelayMs<u32> for Delay {
    #[inline]
    fn delay_ms(&mut self, ms: u32) {
        Delay::delay_ms(self, ms);
    }
}

// This is a workaround to allow `delay_ms(42)` construction without specifying a type.
impl DelayMs<i32> for Delay {
    #[inline(always)]
    fn delay_ms(&mut self, ms: i32) {
        assert!(ms >= 0);
        Delay::delay_ms(self, ms as u32);
    }
}

impl DelayMs<u16> for Delay {
    #[inline(always)]
    fn delay_ms(&mut self, ms: u16) {
        Delay::delay_ms(self, u32::from(ms));
    }
}

impl DelayMs<u8> for Delay {
    #[inline(always)]
    fn delay_ms(&mut self, ms: u8) {
        Delay::delay_ms(self, u32::from(ms));
    }
}

impl DelayUs<u32> for Delay {
    #[inline]
    fn delay_us(&mut self, us: u32) {
        Delay::delay_us(self, us);
    }
}

// This is a workaround to allow `delay_us(42)` construction without specifying a type.
impl DelayUs<i32> for Delay {
    #[inline(always)]
    fn delay_us(&mut self, us: i32) {
        assert!(us >= 0);
        Delay::delay_us(self, us as u32);
    }
}

impl DelayUs<u16> for Delay {
    #[inline(always)]
    fn delay_us(&mut self, us: u16) {
        Delay::delay_us(self, u32::from(us))
    }
}

impl DelayUs<u8> for Delay {
    #[inline(always)]
    fn delay_us(&mut self, us: u8) {
        Delay::delay_us(self, u32::from(us))
    }
}
