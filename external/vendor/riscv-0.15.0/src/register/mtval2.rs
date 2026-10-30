//! mtval register

const MASK: usize = usize::MAX;

read_only_csr! {
    /// mtval2 register
    Mtval2: 0x348,
    mask: MASK,
}

impl Mtval2 {
    /// Represents the bitshift value of the guest-page address stored in `mtval2`.
    pub const GUEST_PAGE_SHIFT: usize = 2;

    /// Gets the guest-page fault physical address.
    ///
    /// # Note
    ///
    /// The address is written when an invalid implicit memory access during address translation.
    pub const fn guest_fault_address(&self) -> usize {
        self.bits() << Self::GUEST_PAGE_SHIFT
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mtval2() {
        (1..=usize::BITS)
            .map(|r| ((1u128 << r) - 1) as usize)
            .for_each(|bits| {
                let mtval2 = Mtval2::from_bits(bits);
                assert_eq!(mtval2.bits(), bits);
                assert_eq!(
                    mtval2.guest_fault_address(),
                    bits << Mtval2::GUEST_PAGE_SHIFT
                );
            });
    }
}
