//! `senvcfg` register.

#[cfg(target_arch = "riscv32")]
const MASK: usize = 0xf5;
#[cfg(not(target_arch = "riscv32"))]
const MASK: usize = 0x3_0000_00fd;

read_write_csr! {
    /// `senvcfg` register.
    Senvcfg: 0x10a,
    mask: MASK,
}

set!(0x10a);
clear!(0x10a);

read_write_csr_field! {
    Senvcfg,
    /// Gets the `fiom` (Fence of I/O Implies Memory) field value.
    fiom: 0,
}

read_write_csr_field! {
    Senvcfg,
    /// Gets the `lpe` (Landing Pad Enable) field value.
    lpe: 2,
}

#[cfg(not(target_arch = "riscv32"))]
read_write_csr_field! {
    Senvcfg,
    /// Gets the `sse` (Shadow Stack Enable) field value.
    sse: 3,
}

csr_field_enum! {
    /// Represents CBIE (Cache Block Invalidate instruction Enable) field of the `senvcfg` CSR.
    Cbie {
        default: IllegalInstruction,
        /// The instruction takes an illegal instruction exception.
        IllegalInstruction = 0b00,
        /// The instruction is executed and performs a flush operation.
        Flush = 0b01,
        /// The instruction is executed and performs an invalidate operation.
        Invalidate = 0b11,
    }
}

read_write_csr_field! {
    Senvcfg,
    /// Gets the `cbie` (Cache Block Invalidate Enable) field value.
    cbie,
    Cbie: [4:5],
}

read_write_csr_field! {
    Senvcfg,
    /// Gets the `cbcfe` (Cache Block Clean and Flush Enable) field value.
    cbcfe: 6,
}

read_write_csr_field! {
    Senvcfg,
    /// Gets the `cbze` (Cache Block Zero Enable) field value.
    cbze: 7,
}

#[cfg(not(target_arch = "riscv32"))]
csr_field_enum! {
    /// Represents PMM (Pointer Masking Mode) field of the `senvcfg` CSR.
    Pmm {
        default: Disabled,
        /// Pointer masking is disabled (PMLEN=0).
        Disabled = 0b00,
        /// Pointer masking is enabled with PMLEN=XLEN-57 (PMLEN=7 on RV64).
        Mask7bit = 0b10,
        /// Pointer masking is enabled with PMLEN=XLEN-48 (PMLEN=16 on RV64).
        Mask16bit = 0b11,
    }
}

#[cfg(not(target_arch = "riscv32"))]
read_write_csr_field! {
    Senvcfg,
    /// Gets the `pmm` (Pointer Masking Mode) field value.
    pmm,
    Pmm: [32:33],
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_senvcfg() {
        let mut senvcfg = Senvcfg::from_bits(0);

        test_csr_field!(senvcfg, fiom);
        test_csr_field!(senvcfg, lpe);

        #[cfg(not(target_arch = "riscv32"))]
        test_csr_field!(senvcfg, sse);

        [Cbie::IllegalInstruction, Cbie::Flush, Cbie::Invalidate]
            .into_iter()
            .for_each(|cbie| {
                test_csr_field!(senvcfg, cbie: cbie);
            });

        test_csr_field!(senvcfg, cbcfe);
        test_csr_field!(senvcfg, cbze);

        #[cfg(not(target_arch = "riscv32"))]
        [Pmm::Disabled, Pmm::Mask7bit, Pmm::Mask16bit]
            .into_iter()
            .for_each(|pmm| {
                test_csr_field!(senvcfg, pmm: pmm);
            });
    }
}
