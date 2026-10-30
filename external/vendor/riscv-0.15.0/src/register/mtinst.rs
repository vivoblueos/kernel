//! mtinst register.

const MASK: usize = usize::MAX;

read_write_csr! {
    /// mtinst register
    Mtinst: 0x34a,
    mask: MASK,
}

read_write_csr_field! {
    Mtinst,
    /// Trapped instruction `opcode` field.
    opcode: [0:6],
}

read_write_csr_field! {
    Mtinst,
    /// Trapped instruction `rd` field for load instructions.
    rd: [7:11],
}

read_write_csr_field! {
    Mtinst,
    /// Trapped instruction `funct3` field.
    funct3: [12:14],
}

read_write_csr_field! {
    Mtinst,
    /// Trapped instruction `address offset` field.
    address_offset: [15:19],
}

read_write_csr_field! {
    Mtinst,
    /// Trapped instruction `rs2` field for store instructions.
    rs2: [20:24],
}

read_write_csr_field! {
    Mtinst,
    /// Trapped instruction `rl` field for atomic instructions.
    rl: 25,
}

read_write_csr_field! {
    Mtinst,
    /// Trapped instruction `aq` field for atomic instructions.
    aq: 26,
}

read_write_csr_field! {
    Mtinst,
    /// Trapped instruction `funct5` field for atomic instructions.
    funct5: [27:31],
}

read_write_csr_field! {
    Mtinst,
    /// Trapped instruction `funct7` field for virtual machine instructions.
    funct7: [25:31],
}

set!(0x34a);
clear!(0x34a);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mtinst() {
        (1..=usize::BITS)
            .map(|r| ((1u128 << r) - 1) as usize)
            .for_each(|bits| {
                let reset = 0;
                let mut mtinst = Mtinst::from_bits(bits);

                test_csr_field!(mtinst, opcode: [0, 6], reset);
                test_csr_field!(mtinst, rd: [7, 11], reset);
                test_csr_field!(mtinst, funct3: [12, 14], reset);
                test_csr_field!(mtinst, address_offset: [15, 19], reset);
                test_csr_field!(mtinst, rs2: [20, 24], reset);
                test_csr_field!(mtinst, rl);
                test_csr_field!(mtinst, aq);
                test_csr_field!(mtinst, funct5: [27, 31], reset);
                test_csr_field!(mtinst, funct7: [25, 31], reset);
            });
    }
}
