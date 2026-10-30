//! sip register

use crate::bits::bf_extract;
use riscv_pac::CoreInterruptNumber;

read_only_csr! {
    /// sip register
    Sip: 0x144,
    mask: usize::MAX,
}

read_only_csr_field! {
    Sip,
    /// Supervisor Software Interrupt Pending
    ssoft: 1,
}

read_only_csr_field! {
    Sip,
    /// Supervisor Timer Interrupt Pending
    stimer: 5,
}

read_only_csr_field! {
    Sip,
    /// Supervisor External Interrupt Pending
    sext: 9,
}

impl Sip {
    /// Returns true when a given interrupt is pending.
    #[inline]
    pub fn is_pending<I: CoreInterruptNumber>(&self, interrupt: I) -> bool {
        bf_extract(self.bits, interrupt.number(), 1) != 0
    }
}

set!(0x144);
clear!(0x144);

set_clear_csr!(
    /// Supervisor Software Interrupt Pending
    , set_ssoft, clear_ssoft, 1 << 1);

/// Clear the pending state of a specific core interrupt source.
///
/// # Safety
///
/// Not all interrupt sources allow clearing of pending interrupts via the `sip` register.
/// Instead, it may be necessary to perform an alternative action to clear the interrupt.
/// Check the specification of your specific core for details.
#[inline]
pub unsafe fn clear_pending<I: CoreInterruptNumber>(interrupt: I) {
    _clear(1 << interrupt.number());
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sip() {
        let sip = Sip::from_bits(0);

        assert!(!sip.stimer());
        assert!(!sip.sext());

        assert!(Sip::from_bits(1 << 5).stimer());
        assert!(Sip::from_bits(1 << 9).sext());
    }
}
