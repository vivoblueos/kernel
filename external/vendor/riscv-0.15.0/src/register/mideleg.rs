//! mideleg register

read_write_csr! {
    /// `mideleg` register
    Mideleg: 0x303,
    mask: 0x222,
}

read_write_csr_field! {
    Mideleg,
    /// Supervisor Software Interrupt Delegate
    ssoft: 1,
}

read_write_csr_field! {
    Mideleg,
    /// Supervisor Timer Interrupt Delegate
    stimer: 5,
}

read_write_csr_field! {
    Mideleg,
    /// Supervisor External Interrupt Delegate
    sext: 9,
}

set!(0x303);
clear!(0x303);

set_clear_csr!(
    /// Supervisor Software Interrupt Delegate
    , set_ssoft, clear_ssoft, 1 << 1);
set_clear_csr!(
    /// Supervisor Timer Interrupt Delegate
    , set_stimer, clear_stimer, 1 << 5);
set_clear_csr!(
    /// Supervisor External Interrupt Delegate
    , set_sext, clear_sext, 1 << 9);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mideleg() {
        let mut m = Mideleg::from_bits(0);

        test_csr_field!(m, ssoft);
        test_csr_field!(m, stimer);
        test_csr_field!(m, sext);
    }
}
