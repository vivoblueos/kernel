//! satp register

use crate::result::{Error, Result};

read_write_csr! {
    /// `satp` register
    Satp: 0x180,
    mask: usize::MAX,
}

#[cfg(target_pointer_width = "32")]
csr_field_enum! {
    /// 32-bit satp mode
    Mode {
        default: Bare,
        /// No translation or protection
        Bare = 0,
        /// Page-based 32-bit virtual addressing
        Sv32 = 1,
    }
}

#[cfg(target_pointer_width = "64")]
csr_field_enum! {
    /// 64-bit satp mode
    Mode {
        default: Bare,
        /// No translation or protection
        Bare = 0,
        /// Page-based 39-bit virtual addressing
        Sv39 = 8,
        /// Page-based 48-bit virtual addressing
        Sv48 = 9,
        /// Page-based 57-bit virtual addressing
        Sv57 = 10,
        /// Page-based 64-bit virtual addressing
        Sv64 = 11,
    }
}

#[cfg(target_pointer_width = "32")]
read_write_csr_field! {
    Satp,
    /// Physical page number
    ppn: [0:21],
}

#[cfg(target_pointer_width = "64")]
read_write_csr_field! {
    Satp,
    /// Physical page number
    ppn: [0:43],
}

#[cfg(target_pointer_width = "32")]
read_write_csr_field! {
    Satp,
    /// Address space identifier
    asid: [22:30],
}

#[cfg(target_pointer_width = "64")]
read_write_csr_field! {
    Satp,
    /// Address space identifier
    asid: [44:59],
}

#[cfg(target_pointer_width = "32")]
read_write_csr_field! {
    Satp,
    /// Current address-translation scheme.
    mode,
    Mode: [31:31],
}

#[cfg(target_pointer_width = "64")]
read_write_csr_field! {
    Satp,
    /// Current address-translation scheme.
    mode,
    Mode: [60:63],
}

/// Sets the register to corresponding page table mode, physical page number and address space id.
///
/// **WARNING**: panics on:
///
/// - non-`riscv` targets
/// - invalid field values
#[inline]
#[cfg(target_pointer_width = "32")]
pub unsafe fn set(mode: Mode, asid: usize, ppn: usize) {
    try_set(mode, asid, ppn).unwrap();
}

/// Attempts to set the register to corresponding page table mode, physical page number and address space id.
#[inline]
#[cfg(target_pointer_width = "32")]
pub unsafe fn try_set(mode: Mode, asid: usize, ppn: usize) -> Result<()> {
    if asid != asid & 0x1FF {
        Err(Error::InvalidFieldValue {
            field: "asid",
            value: asid,
            bitmask: 0x1FF,
        })
    } else if ppn != ppn & 0x3F_FFFF {
        Err(Error::InvalidFieldValue {
            field: "ppn",
            value: ppn,
            bitmask: 0x3F_FFFF,
        })
    } else {
        let bits = (mode as usize) << 31 | (asid << 22) | ppn;
        _try_write(bits)
    }
}

/// Sets the register to corresponding page table mode, physical page number and address space id.
///
/// **WARNING**: panics on:
///
/// - non-`riscv` targets
/// - invalid field values
#[inline]
#[cfg(target_pointer_width = "64")]
pub unsafe fn set(mode: Mode, asid: usize, ppn: usize) {
    try_set(mode, asid, ppn).unwrap()
}

/// Attempts to set the register to corresponding page table mode, physical page number and address space id.
#[inline]
#[cfg(target_pointer_width = "64")]
pub unsafe fn try_set(mode: Mode, asid: usize, ppn: usize) -> Result<()> {
    if asid != asid & 0xFFFF {
        Err(Error::InvalidFieldValue {
            field: "asid",
            value: asid,
            bitmask: 0xFFFF,
        })
    } else if ppn != ppn & 0xFFF_FFFF_FFFF {
        Err(Error::InvalidFieldValue {
            field: "ppn",
            value: ppn,
            bitmask: 0xFFF_FFFF_FFFF,
        })
    } else {
        let bits = ((mode as usize) << 60) | (asid << 44) | ppn;
        _try_write(bits)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(target_pointer_width = "32")]
    const ASID_START: usize = 22;
    #[cfg(target_pointer_width = "64")]
    const ASID_START: usize = 44;
    #[cfg(target_pointer_width = "32")]
    const MODE_START: usize = 31;
    #[cfg(target_pointer_width = "64")]
    const MODE_START: usize = 60;

    #[cfg(target_pointer_width = "32")]
    const MODES: [Mode; 2] = [Mode::Bare, Mode::Sv32];
    #[cfg(target_pointer_width = "64")]
    const MODES: [Mode; 5] = [Mode::Bare, Mode::Sv39, Mode::Sv48, Mode::Sv57, Mode::Sv64];

    #[test]
    fn test_satp() {
        let new_mode = Mode::new();

        (1..=usize::BITS)
            .map(|r| ((1u128 << r) - 1) as usize)
            .for_each(|raw| {
                let mut satp = Satp::from_bits(raw);

                let exp_ppn = raw & ((1usize << ASID_START) - 1);
                let exp_asid = (raw & ((1usize << MODE_START) - 1)) >> ASID_START;

                assert_eq!(satp.ppn(), exp_ppn);

                satp.set_ppn(0);
                assert_eq!(satp.ppn(), 0);

                satp.set_ppn(exp_ppn);
                assert_eq!(satp.ppn(), exp_ppn);

                assert_eq!(satp.asid(), exp_asid);

                satp.set_asid(0);
                assert_eq!(satp.asid(), 0);

                satp.set_asid(exp_asid);
                assert_eq!(satp.asid(), exp_asid);

                match Mode::from_usize(raw >> 60) {
                    Ok(exp_mode) => {
                        assert_eq!(satp.try_mode(), Ok(exp_mode));
                        assert_eq!(satp.mode(), exp_mode);

                        satp.set_mode(new_mode);

                        assert_eq!(satp.try_mode(), Ok(new_mode));
                        assert_eq!(satp.mode(), new_mode);

                        satp.set_mode(exp_mode);

                        assert_eq!(satp.try_mode(), Ok(exp_mode));
                        assert_eq!(satp.mode(), exp_mode);
                    }
                    Err(exp_err) => {
                        assert_eq!(satp.try_mode(), Err(exp_err));
                    }
                }
            });

        let mut satp = Satp::from_bits(0);
        MODES
            .into_iter()
            .for_each(|mode| test_csr_field!(satp, mode: mode));
    }
}
