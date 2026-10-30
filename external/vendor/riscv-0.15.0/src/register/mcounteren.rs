//! mcounteren register

use crate::result::{Error, Result};

read_write_csr! {
    /// `mcounteren` register
    Mcounteren: 0x306,
    mask: 0xffff_ffff,
}

read_write_csr_field! {
    Mcounteren,
    /// Supervisor "cycle\[h\]" Enable
    cy: 0,
}

read_write_csr_field! {
    Mcounteren,
    /// Supervisor "time\[h\]" Enable
    tm: 1,
}

read_write_csr_field! {
    Mcounteren,
    /// Supervisor "instret\[h\]" Enable
    ir: 2,
}

read_write_csr_field! {
    Mcounteren,
    /// Supervisor "hpm\[x\]" Enable (bits 3-31)
    hpm: 3..=31,
}

set!(0x306);
clear!(0x306);

set_clear_csr!(
/// Supervisor cycle Enable
    , set_cy, clear_cy, 1 << 0);

set_clear_csr!(
/// Supervisor time Enable
    , set_tm, clear_tm, 1 << 1);

set_clear_csr!(
/// Supervisor instret Enable
    , set_ir, clear_ir, 1 << 2);

/// Enables the "hpm\[X\]" counter.
///
/// Updates the `mcounteren` register.
///
/// **WARNING**: panics on:
///
/// - non-`riscv` targets
/// - `index` out-of-bounds
#[inline]
pub unsafe fn set_hpm(index: usize) {
    try_set_hpm(index).unwrap();
}

/// Attempts to enable the "hpm\[X\]" counter.
///
/// Updates the `mcounteren` register.
#[inline]
pub unsafe fn try_set_hpm(index: usize) -> Result<()> {
    if (3..32).contains(&index) {
        _try_set(1 << index)
    } else {
        Err(Error::IndexOutOfBounds {
            index,
            min: 3,
            max: 31,
        })
    }
}

/// Disables the "hpm\[X\]" counter.
///
/// Updates the `mcounteren` register.
///
/// **WARNING**: panics on:
///
/// - non-`riscv` targets
/// - `index` out-of-bounds
#[inline]
pub unsafe fn clear_hpm(index: usize) {
    try_clear_hpm(index).unwrap();
}

/// Attempts to disable the "hpm\[X\]" counter.
///
/// Updates the `mcounteren` register.
#[inline]
pub unsafe fn try_clear_hpm(index: usize) -> Result<()> {
    if (3..32).contains(&index) {
        _try_clear(1 << index)
    } else {
        Err(Error::IndexOutOfBounds {
            index,
            min: 3,
            max: 31,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mcounteren() {
        let mut m = Mcounteren { bits: 0 };

        test_csr_field!(m, cy);
        test_csr_field!(m, tm);
        test_csr_field!(m, ir);

        (3..32).for_each(|i| test_csr_field!(m, hpm, i));

        (0..3).chain(32..64).for_each(|index| {
            test_csr_field!(
                m,
                hpm,
                index,
                Error::IndexOutOfBounds {
                    index,
                    min: 3,
                    max: 31
                }
            )
        });
    }
}
