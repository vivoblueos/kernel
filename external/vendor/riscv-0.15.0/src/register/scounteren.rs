//! scounteren register

use crate::result::{Error, Result};

read_write_csr! {
    /// scounteren register
    Scounteren: 0x106,
    mask: 0xffff_ffff,
}

read_write_csr_field! {
    Scounteren,
    /// User "cycle\[h\]" Enable
    cy: 0,
}

read_write_csr_field! {
    Scounteren,
    /// User "time\[h\]" Enable
    tm: 1,
}

read_write_csr_field! {
    Scounteren,
    /// User "instret\[h]\" Enable
    ir: 2,
}

read_write_csr_field! {
    Scounteren,
    /// User "hpm\[x\]" Enable (bits 3-31)
    hpm: 3..=31,
}

set!(0x106);
clear!(0x106);

set_clear_csr!(
/// User cycle Enable
    , set_cy, clear_cy, 1 << 0);

set_clear_csr!(
/// User time Enable
    , set_tm, clear_tm, 1 << 1);

set_clear_csr!(
/// User instret Enable
    , set_ir, clear_ir, 1 << 2);

/// Sets the "hpm\[x\]" enable (bits 3-31).
///
/// # Note
///
/// Panics if `index` is out-of-bounds.
#[inline]
pub unsafe fn set_hpm(index: usize) {
    try_set_hpm(index).unwrap();
}

/// Attempts to set the "hpm\[x\]" enable (bits 3-31).
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

/// Clears the "hpm\[x\]" enable (bits 3-31).
///
/// # Note
///
/// Panics if `index` is out-of-bounds.
#[inline]
pub unsafe fn clear_hpm(index: usize) {
    try_clear_hpm(index).unwrap()
}

/// Attempts to clear the "hpm\[x\]" enable (bits 3-31).
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
    fn test_scounteren() {
        const HPM_MIN: usize = 3;
        const HPM_MAX: usize = 31;

        let mut scounteren = Scounteren::from_bits(0);

        test_csr_field!(scounteren, cy);
        test_csr_field!(scounteren, tm);
        test_csr_field!(scounteren, ir);

        (HPM_MIN..=HPM_MAX).for_each(|index| {
            test_csr_field!(scounteren, hpm, index);
        });

        (0..usize::BITS as usize)
            .filter(|&i| !(HPM_MIN..=HPM_MAX).any(|idx| idx == i))
            .for_each(|index| {
                let err = Error::IndexOutOfBounds {
                    index,
                    min: 3,
                    max: 31,
                };
                test_csr_field!(scounteren, hpm, index, err)
            });
    }
}
