//! `mcountinhibit` register

use crate::result::{Error, Result};

read_write_csr! {
    /// `mcountinhibit` register
    Mcountinhibit: 0x320,
    mask: 0xffff_fffd,
}

set!(0x320);
clear!(0x320);

read_write_csr_field! {
    Mcountinhibit,
    /// Gets the `cycle[h]` inhibit field value.
    cy: 0,
}

read_write_csr_field! {
    Mcountinhibit,
    /// Gets the `instret[h]` inhibit field value.
    ir: 2,
}

read_write_csr_field! {
    Mcountinhibit,
    /// Gets the `mhpmcounterX[h]` inhibit field value.
    ///
    /// **WARN**: `index` must be in the range `[31:3]`.
    hpm: 3..=31,
}

set_clear_csr!(
/// Machine cycle Disable
    , set_cy, clear_cy, 1 << 0);

set_clear_csr!(
/// Machine instret Disable
    , set_ir, clear_ir, 1 << 2);

#[inline]
pub unsafe fn set_hpm(index: usize) {
    try_set_hpm(index).unwrap();
}

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

#[inline]
pub unsafe fn clear_hpm(index: usize) {
    try_clear_hpm(index).unwrap();
}

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
    fn test_mcountinhibit() {
        let mut m = Mcountinhibit { bits: 0 };

        assert!(!m.cy());

        m.set_cy(true);
        assert!(m.cy());

        m.set_cy(false);
        assert!(!m.cy());

        assert!(!m.ir());

        m.set_ir(true);
        assert!(m.ir());

        m.set_ir(false);
        assert!(!m.ir());

        (3..32).for_each(|i| {
            assert!(!m.hpm(i));
            assert_eq!(m.try_hpm(i), Ok(false));

            m.set_hpm(i, true);
            assert!(m.hpm(i));
            assert_eq!(m.try_hpm(i), Ok(true));

            assert_eq!(m.try_set_hpm(i, false), Ok(()));
            assert_eq!(m.try_hpm(i), Ok(false));
        });

        (0..2).chain(32..64).for_each(|index| {
            assert_eq!(
                m.try_hpm(index),
                Err(Error::IndexOutOfBounds {
                    index,
                    min: 3,
                    max: 31
                })
            );
            assert_eq!(
                m.try_set_hpm(index, false),
                Err(Error::IndexOutOfBounds {
                    index,
                    min: 3,
                    max: 31
                })
            );
        });
    }
}
