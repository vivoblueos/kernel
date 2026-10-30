//! `mconfigptr` register.

use crate::result::{Error, Result};

const MASK: usize = usize::MAX;

read_only_csr! {
    /// `mconfigptr` register.
    Mconfigptr: 0xf15,
    mask: MASK,
    sentinel: 0,
}

impl Mconfigptr {
    /// Represents the bitshift for a properly aligned configuration pointer.
    pub const ALIGN_SHIFT: usize = (usize::BITS / 8).ilog2() as usize;
    /// Represents the bitmask for a properly aligned configuration pointer.
    pub const ALIGN_MASK: usize = (1usize << Self::ALIGN_SHIFT) - 1;

    /// Gets the pointer to the machine configuration structure.
    ///
    /// # Panics
    ///
    /// Panics if:
    ///
    /// - the value is `0`, indicating no configuration structure
    /// - the pointer is not aligned to an MXLEN byte value
    pub fn as_ptr(&self) -> *const u8 {
        self.try_as_ptr().unwrap()
    }

    /// Attempts to get the pointer to the machine configuration structure.
    ///
    /// # Note
    ///
    /// Returns an error if:
    ///
    /// - the value is `0`, indicating no configuration structure
    /// - the pointer is not aligned to an MXLEN byte value
    pub const fn try_as_ptr(&self) -> Result<*const u8> {
        match self.bits() {
            0 => Err(Error::InvalidFieldVariant {
                field: "mconfigptr",
                value: 0,
            }),
            p if p & Self::ALIGN_MASK != 0 => Err(Error::InvalidFieldValue {
                field: "mconfigptr",
                value: p,
                bitmask: !Self::ALIGN_MASK,
            }),
            p => Ok(p as *const _),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mconfigptr() {
        #[cfg(target_arch = "riscv32")]
        const EXP_SHIFT: usize = 2;
        #[cfg(not(target_arch = "riscv32"))]
        const EXP_SHIFT: usize = 3;

        const EXP_MASK: usize = (1usize << EXP_SHIFT) - 1;

        assert_eq!(Mconfigptr::ALIGN_SHIFT, EXP_SHIFT);
        assert_eq!(Mconfigptr::ALIGN_MASK, EXP_MASK);

        (1..usize::BITS)
            .map(|b| ((1u128 << b) - 1) as usize)
            .for_each(|ptr| {
                let mconfigptr = Mconfigptr::from_bits(ptr);
                assert_eq!(mconfigptr.bits(), ptr);

                match mconfigptr.try_as_ptr() {
                    Ok(cfg_ptr) => {
                        assert_eq!(cfg_ptr, ptr as *const _);
                        assert_eq!(mconfigptr.as_ptr(), ptr as *const _);
                    }
                    Err(err) if ptr == 0 => assert_eq!(
                        err,
                        Error::InvalidFieldVariant {
                            field: "mconfigptr",
                            value: 0
                        }
                    ),
                    Err(err) => assert_eq!(
                        err,
                        Error::InvalidFieldValue {
                            field: "mconfigptr",
                            value: ptr,
                            bitmask: !Mconfigptr::ALIGN_MASK,
                        }
                    ),
                }

                let aligned_ptr = ptr << Mconfigptr::ALIGN_SHIFT;
                let aligned_mconfigptr = Mconfigptr::from_bits(aligned_ptr);

                assert_eq!(aligned_mconfigptr.try_as_ptr(), Ok(aligned_ptr as *const _));
                assert_eq!(aligned_mconfigptr.as_ptr(), aligned_ptr as *const _);
            });
    }
}
