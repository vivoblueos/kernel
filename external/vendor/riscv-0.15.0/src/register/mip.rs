//! mip register

use crate::bits::bf_extract;
use riscv_pac::CoreInterruptNumber;

read_only_csr! {
    /// `mip` register
    Mip: 0x344,
    mask: usize::MAX,
}

read_only_csr_field! {
    Mip,
    /// Supervisor Software Interrupt Pending
    ssoft: 1,
}

read_only_csr_field! {
    Mip,
    /// Machine Software Interrupt Pending
    msoft: 3,
}

read_only_csr_field! {
    Mip,
    /// Supervisor Timer Interrupt Pending
    stimer: 5,
}

read_only_csr_field! {
    Mip,
    /// Machine Timer Interrupt Pending
    mtimer: 7,
}

read_only_csr_field! {
    Mip,
    /// Supervisor External Interrupt Pending
    sext: 9,
}

read_only_csr_field! {
    Mip,
    /// Machine External Interrupt Pending
    mext: 11,
}

impl Mip {
    /// Returns true when a given interrupt is pending.
    #[inline]
    pub fn is_pending<I: CoreInterruptNumber>(&self, interrupt: I) -> bool {
        bf_extract(self.bits, interrupt.number(), 1) != 0
    }
}

set!(0x344);
clear!(0x344);

set_clear_csr!(
    /// Supervisor Software Interrupt Pending
    , set_ssoft, clear_ssoft, 1 << 1);
set_clear_csr!(
    /// Supervisor Timer Interrupt Pending
    , set_stimer, clear_stimer, 1 << 5);
set_clear_csr!(
    /// Supervisor External Interrupt Pending
    , set_sext, clear_sext, 1 << 9);

/// Clear the pending state of a specific core interrupt source.
///
/// # Safety
///
/// Not all interrupt sources allow clearing of pending interrupts via the `mip` register.
/// Instead, it may be necessary to perform an alternative action to clear the interrupt.
/// Check the specification of your target chip for details.
#[inline]
pub unsafe fn clear_pending<I: CoreInterruptNumber>(interrupt: I) {
    _clear(1 << interrupt.number());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mip() {
        let mip = Mip::from_bits(0);

        assert!(!mip.msoft());
        assert!(!mip.mtimer());
        assert!(!mip.mext());

        assert!(Mip::from_bits(1 << 3).msoft());
        assert!(Mip::from_bits(1 << 7).mtimer());
        assert!(Mip::from_bits(1 << 11).mext());
    }
}
