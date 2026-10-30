//! mtvec register

use crate::result::{Error, Result};

const MASK: usize = usize::MAX;
const TRAP_MASK: usize = 0b11;

read_write_csr! {
    /// mtvec register
    Mtvec: 0x305,
    mask: MASK,
}

csr_field_enum! {
    /// Trap mode
    TrapMode {
        default: Direct,
        Direct = 0,
        Vectored = 1,
    }
}

read_write_csr_field! {
    Mtvec,
    /// Accesses the trap-vector mode.
    trap_mode,
    TrapMode: [0:1],
}

impl Mtvec {
    /// Creates a new `Mtvec` with the given address and trap mode.
    ///
    /// # Note
    ///
    /// Panics if the address is not aligned to 4-bytes.
    #[inline]
    pub fn new(address: usize, trap_mode: TrapMode) -> Self {
        Self::try_new(address, trap_mode).unwrap()
    }

    /// Attempts to create a new `Mtvec` with the given address and trap mode.
    #[inline]
    pub fn try_new(address: usize, trap_mode: TrapMode) -> Result<Self> {
        let mut mtvec = Self::from_bits(0);
        mtvec.try_set_address(address)?;
        mtvec.set_trap_mode(trap_mode);
        Ok(mtvec)
    }

    /// Returns the trap-vector base-address
    #[inline]
    pub const fn address(&self) -> usize {
        self.bits & !TRAP_MASK
    }

    /// Sets the trap-vector base-address.
    ///
    /// # Note
    ///
    /// Panics if the address is not aligned to 4-bytes.
    #[inline]
    pub fn set_address(&mut self, address: usize) {
        self.try_set_address(address).unwrap();
    }

    /// Attempts to set the trap-vector base-address.
    ///
    /// # Note
    ///
    /// Returns an error if the address is not aligned to 4-bytes.
    #[inline]
    pub fn try_set_address(&mut self, address: usize) -> Result<()> {
        // check for four-byte alignment
        if (address & TRAP_MASK) != 0 {
            Err(Error::InvalidFieldVariant {
                field: "mtvec::address",
                value: address,
            })
        } else {
            self.bits = address | (self.bits & TRAP_MASK);
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mtvec() {
        let mut m = Mtvec::from_bits(0);

        (1..=usize::BITS)
            .map(|r| (((1u128 << r) - 1) as usize) & !TRAP_MASK)
            .for_each(|address| {
                m.set_address(address);
                assert_eq!(m.address(), address);

                assert_eq!(m.try_set_address(address), Ok(()));
                assert_eq!(m.address(), address);
            });

        (1..=usize::BITS)
            .filter_map(|r| match ((1u128 << r) - 1) as usize {
                addr if (addr & TRAP_MASK) != 0 => Some(addr),
                _ => None,
            })
            .for_each(|address| {
                assert_eq!(
                    m.try_set_address(address),
                    Err(Error::InvalidFieldVariant {
                        field: "mtvec::address",
                        value: address,
                    })
                );
            });

        test_csr_field!(m, trap_mode: TrapMode::Direct);
        test_csr_field!(m, trap_mode: TrapMode::Vectored);
    }
}
