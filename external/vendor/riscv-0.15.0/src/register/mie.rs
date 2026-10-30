//! mie register

use crate::bits::{bf_extract, bf_insert};
use riscv_pac::CoreInterruptNumber;

read_write_csr! {
    /// `mie` register
    Mie: 0x304,
    mask: usize::MAX,
}

read_write_csr_field! {
    Mie,
    /// Supervisor Software Interrupt Enable
    ssoft: 1,
}

read_write_csr_field! {
    Mie,
    /// Machine Software Interrupt Enable
    msoft: 3,
}

read_write_csr_field! {
    Mie,
    /// Supervisor Timer Interrupt Enable
    stimer: 5,
}

read_write_csr_field! {
    Mie,
    /// Machine Timer Interrupt Enable
    mtimer: 7,
}

read_write_csr_field! {
    Mie,
    /// Supervisor External Interrupt Enable
    sext: 9,
}

read_write_csr_field! {
    Mie,
    /// Machine External Interrupt Enable
    mext: 11,
}

impl Mie {
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

set!(0x304);
clear!(0x304);

set_clear_csr!(
    /// Supervisor Software Interrupt Enable
    , set_ssoft, clear_ssoft, 1 << 1);
set_clear_csr!(
    /// Machine Software Interrupt Enable
    , set_msoft, clear_msoft, 1 << 3);
set_clear_csr!(
    /// Supervisor Timer Interrupt Enable
    , set_stimer, clear_stimer, 1 << 5);
set_clear_csr!(
    /// Machine Timer Interrupt Enable
    , set_mtimer, clear_mtimer, 1 << 7);
set_clear_csr!(
    /// Supervisor External Interrupt Enable
    , set_sext, clear_sext, 1 << 9);
set_clear_csr!(
    /// Machine External Interrupt Enable
    , set_mext, clear_mext, 1 << 11);

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
    use crate::interrupt::machine::Interrupt;

    #[test]
    fn test_mie() {
        let mut m = Mie::from_bits(0);

        test_csr_field!(m, ssoft);
        test_csr_field!(m, msoft);
        test_csr_field!(m, stimer);
        test_csr_field!(m, mtimer);
        test_csr_field!(m, sext);
        test_csr_field!(m, mext);
    }

    #[test]
    fn test_mie_interrupt() {
        let mut m = Mie::from_bits(0);

        m.enable(Interrupt::SupervisorSoft);
        assert!(m.is_enabled(Interrupt::SupervisorSoft));
        m.disable(Interrupt::SupervisorSoft);
        assert!(!m.is_enabled(Interrupt::SupervisorSoft));

        m.enable(Interrupt::MachineSoft);
        assert!(m.is_enabled(Interrupt::MachineSoft));
        m.disable(Interrupt::MachineSoft);
        assert!(!m.is_enabled(Interrupt::MachineSoft));

        m.enable(Interrupt::SupervisorTimer);
        assert!(m.is_enabled(Interrupt::SupervisorTimer));
        m.disable(Interrupt::SupervisorTimer);
        assert!(!m.is_enabled(Interrupt::SupervisorTimer));

        m.enable(Interrupt::MachineTimer);
        assert!(m.is_enabled(Interrupt::MachineTimer));
        m.disable(Interrupt::MachineTimer);
        assert!(!m.is_enabled(Interrupt::MachineTimer));

        m.enable(Interrupt::SupervisorExternal);
        assert!(m.is_enabled(Interrupt::SupervisorExternal));
        m.disable(Interrupt::SupervisorExternal);
        assert!(!m.is_enabled(Interrupt::SupervisorExternal));

        m.enable(Interrupt::MachineExternal);
        assert!(m.is_enabled(Interrupt::MachineExternal));
        m.disable(Interrupt::MachineExternal);
        assert!(!m.is_enabled(Interrupt::MachineExternal));
    }
}
