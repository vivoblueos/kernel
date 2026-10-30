//! `scontext` register.

#[cfg(target_arch = "riscv32")]
const MASK: usize = 0xffff;
#[cfg(not(target_arch = "riscv32"))]
const MASK: usize = 0xffff_ffff;

read_write_csr! {
    /// `scontext` register.
    Scontext: 0x5a8,
    mask: MASK,
}

set!(0x5a8);
clear!(0x5a8);

#[cfg(target_arch = "riscv32")]
read_write_csr_field! {
    Scontext,
    /// Represents the `data` context number of the `scontext` CSR.
    data: [0:15],
}

#[cfg(not(target_arch = "riscv32"))]
read_write_csr_field! {
    Scontext,
    /// Represents the `data` context number of the `scontext` CSR.
    data: [0:31],
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scontext() {
        #[cfg(target_arch = "riscv32")]
        const DATA_BITS: usize = 16;
        #[cfg(not(target_arch = "riscv32"))]
        const DATA_BITS: usize = 32;

        let mut scontext = Scontext::from_bits(0);

        (1..=DATA_BITS)
            .map(|b| ((1u64 << b) - 1) as usize)
            .for_each(|data| {
                scontext.set_data(data);
                assert_eq!(scontext.data(), data);
                assert_eq!(scontext.bits(), data);
            });
    }
}
