//! mseccfg register

#[cfg(not(target_arch = "riscv32"))]
const MASK: usize = 0x3_0000_0707;
#[cfg(target_arch = "riscv32")]
const MASK: usize = 0x707;

read_write_csr! {
    /// mseccfg register
    Mseccfg: 0x747,
    mask: MASK,
}

read_write_csr_field! {
    Mseccfg,
    /// Machine-Mode Lockdown
    ///
    /// # Note
    ///
    /// Defined in in the [Smepmp](https://raw.githubusercontent.com/riscv/riscv-tee/main/Smepmp/Smepmp.pdf) extension.
    mml: 0,
}

read_write_csr_field! {
    Mseccfg,
    /// Machine-Mode Whitelist Policy
    ///
    /// # Note
    ///
    /// Defined in in the [Smepmp](https://raw.githubusercontent.com/riscv/riscv-tee/main/Smepmp/Smepmp.pdf) extension.
    mmwp: 1,
}

read_write_csr_field! {
    Mseccfg,
    /// Rule Locking Bypass
    ///
    /// # Note
    ///
    /// Defined in in the [Smepmp](https://raw.githubusercontent.com/riscv/riscv-tee/main/Smepmp/Smepmp.pdf) extension.
    rlb: 2,
}

read_write_csr_field! {
    Mseccfg,
    /// User-mode seed
    ///
    /// # Note
    ///
    /// Defined in in the [Zkr](https://github.com/riscv/riscv-crypto/releases/download/v1.0.1-scalar/riscv-crypto-spec-scalar-v1.0.1.pdf) extension.
    useed: 8,
}

read_write_csr_field! {
    Mseccfg,
    /// Supervisor-mode seed
    ///
    /// # Note
    ///
    /// Defined in in the [Zkr](https://github.com/riscv/riscv-crypto/releases/download/v1.0.1-scalar/riscv-crypto-spec-scalar-v1.0.1.pdf) extension.
    sseed: 9,
}

read_write_csr_field! {
    Mseccfg,
    /// Machine-mode Landing Pad Enable
    ///
    /// # Note
    ///
    /// Defined in in the [Zicfilp](https://github.com/riscv/riscv-cfi/releases/download/v1.0/riscv-cfi.pdf) extension.
    mlpe: 10,
}

csr_field_enum! {
    /// Pointer Masking Machine-mode
    PMM {
        default: Disabled,
        Disabled = 0,
        EnabledXlen57 = 2,
        EnabledXlen48 = 3,
    }
}

#[cfg(not(target_arch = "riscv32"))]
read_write_csr_field! {
    Mseccfg,
    /// Pointer Masking Machine-mode
    ///
    /// # Note
    ///
    /// Defined in in the [Smmpm](https://github.com/riscv/riscv-j-extension/releases/download/pointer-masking-ratified/pointer-masking-ratified.pdf) extension.
    pmm,
    PMM: [32:33],
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mseccfg() {
        let mut mseccfg = Mseccfg::from_bits(0);

        test_csr_field!(mseccfg, mml);
        test_csr_field!(mseccfg, mmwp);
        test_csr_field!(mseccfg, rlb);
        test_csr_field!(mseccfg, useed);
        test_csr_field!(mseccfg, sseed);
        test_csr_field!(mseccfg, mlpe);

        #[cfg(not(target_arch = "riscv32"))]
        {
            test_csr_field!(mseccfg, pmm: PMM::Disabled);
            test_csr_field!(mseccfg, pmm: PMM::EnabledXlen57);
            test_csr_field!(mseccfg, pmm: PMM::EnabledXlen48);
        }
    }
}
