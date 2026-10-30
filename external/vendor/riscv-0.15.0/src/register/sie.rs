//! sie register

use crate::bits::{bf_extract, bf_insert};
use riscv_pac::CoreInterruptNumber;

read_write_csr! {
/// sie register
    Sie: 0x104,
    mask: usize::MAX,
}

read_write_csr_field! {
    Sie,
    /// Supervisor Software Interrupt Enable
    ssoft: 1,
}

read_write_csr_field! {
    Sie,
    /// Supervisor Timer Interrupt Enable
    stimer: 5,
}

read_write_csr_field! {
    Sie,
    /// Supervisor Timer Interrupt Enable
    sext: 9,
}

impl Sie {
    /// Check if a specific core interrupt source is enabled.
    #[inline]
    pub fn is_enabled<I: CoreInterruptNumber>(&self, interrupt: I) -> bool {
        bf_extract(self.bits, interrupt.number(), 1) != 0
    }

    /// Enable a specific core interrupt source.
    #[inline]
    pub fn enable<I: CoreInterruptNumber>(&mut self, interrupt: I) {
        self.bits = bf_insert(self.bits, interrupt.number(), 1, 1);
    }

    /// Disable a specific core interrupt source.
    #[inline]
    pub fn disable<I: CoreInterruptNumber>(&mut self, interrupt: I) {
        self.bits = bf_insert(self.bits, interrupt.number(), 1, 0);
    }
}

set!(0x104);
clear!(0x104);

set_clear_csr!(
    /// Supervisor Software Interrupt Enable
    , set_ssoft, clear_ssoft, 1 << 1);
set_clear_csr!(
    /// Supervisor Timer Interrupt Enable
    , set_stimer, clear_stimer, 1 << 5);
set_clear_csr!(
    /// Supervisor External Interrupt Enable
    , set_sext, clear_sext, 1 << 9);

/// Disables a specific core interrupt source.
#[inline]
pub fn disable<I: CoreInterruptNumber>(interrupt: I) {
    // SAFETY: it is safe to disable an interrupt source
    unsafe { _clear(1 << interrupt.number()) };
}

/// Enables a specific core interrupt source.
///
/// # Safety
///
/// Enabling interrupts might break critical sections or other synchronization mechanisms.
/// Ensure that this is called in a safe context where interrupts can be enabled.
#[inline]
pub unsafe fn enable<I: CoreInterruptNumber>(interrupt: I) {
    unsafe { _set(1 << interrupt.number()) };
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interrupt::supervisor::Interrupt;

    #[test]
    fn test_sie() {
        let mut sie = Sie::from_bits(0);

        test_csr_field!(sie, ssoft);
        test_csr_field!(sie, stimer);
        test_csr_field!(sie, sext);
    }

    #[test]
    fn test_sie_interrupt() {
        let mut s = Sie::from_bits(0);

        s.enable(Interrupt::SupervisorSoft);
        assert!(s.is_enabled(Interrupt::SupervisorSoft));
        s.disable(Interrupt::SupervisorSoft);
        assert!(!s.is_enabled(Interrupt::SupervisorSoft));

        s.enable(Interrupt::SupervisorTimer);
        assert!(s.is_enabled(Interrupt::SupervisorTimer));
        s.disable(Interrupt::SupervisorTimer);
        assert!(!s.is_enabled(Interrupt::SupervisorTimer));

        s.enable(Interrupt::SupervisorExternal);
        assert!(s.is_enabled(Interrupt::SupervisorExternal));
        s.disable(Interrupt::SupervisorExternal);
        assert!(!s.is_enabled(Interrupt::SupervisorExternal));
    }
}
