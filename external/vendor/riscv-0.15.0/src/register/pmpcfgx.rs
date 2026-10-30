//! Physical memory protection configuration

use crate::result::{Error, Result};

csr_field_enum! {
    /// Permission enum contains all possible permission modes for pmp registers
    Permission {
        default: NONE,
        NONE = 0b000,
        R = 0b001,
        W = 0b010,
        RW = 0b011,
        X = 0b100,
        RX = 0b101,
        WX = 0b110,
        RWX = 0b111,
    }
}

impl TryFrom<u8> for Permission {
    type Error = Error;

    fn try_from(val: u8) -> Result<Self> {
        Self::from_usize(val as usize)
    }
}

csr_field_enum! {
    /// Range enum contains all possible addressing modes for pmp registers
    Range {
        default: OFF,
        OFF = 0b00,
        TOR = 0b01,
        NA4 = 0b10,
        NAPOT = 0b11,
    }
}

impl TryFrom<u8> for Range {
    type Error = Error;

    fn try_from(val: u8) -> Result<Self> {
        Self::from_usize(val as usize)
    }
}

/// Pmp struct holds a high-level representation of a single pmp configuration
#[derive(Clone, Copy, Debug)]
pub struct Pmp {
    /// raw bits
    pub byte: u8,
    /// Current PMP Permission
    pub permission: Permission,
    /// Current PMP Range
    pub range: Range,
    /// Is PMP locked?
    pub locked: bool,
}

pub struct Pmpcsr {
    /// Holds the raw contents of a PMP CSR Register
    pub bits: usize,
}

impl Pmpcsr {
    /// Take the register contents and translate into a Pmp configuration struct
    ///
    /// **WARNING**: panics on:
    ///
    /// - non-`riscv` targets
    /// - `index` is out of bounds
    /// - register fields contain invalid values
    #[inline]
    pub fn into_config(&self, index: usize) -> Pmp {
        self.try_into_config(index).unwrap()
    }

    /// Attempts to take the register contents, and translate into a Pmp configuration struct.
    #[inline]
    pub fn try_into_config(&self, index: usize) -> Result<Pmp> {
        let max = match () {
            #[cfg(target_arch = "riscv32")]
            () => Ok(4usize),
            #[cfg(target_arch = "riscv64")]
            () => Ok(8usize),
            #[cfg(not(any(target_arch = "riscv32", target_arch = "riscv64")))]
            () => Err(Error::Unimplemented),
        }?;

        if index < max {
            let byte = (self.bits >> (8 * index)) as u8; // move config to LSB and drop the rest
            let permission = byte & 0x7; // bits 0-2
            let range = (byte >> 3) & 0x3; // bits 3-4

            Ok(Pmp {
                byte,
                permission: permission.try_into()?,
                range: range.try_into()?,
                locked: (byte & (1 << 7)) != 0,
            })
        } else {
            Err(Error::IndexOutOfBounds {
                index,
                min: 0,
                max: max - 1,
            })
        }
    }
}

/// Physical memory protection configuration
/// pmpcfg0 struct contains pmp0cfg - pmp3cfg for RV32, and pmp0cfg - pmp7cfg for RV64
pub mod pmpcfg0 {
    use super::{Permission, Pmpcsr, Range};

    read_csr_as!(Pmpcsr, 0x3A0);
    write_csr_as_usize!(0x3A0);

    set_pmp!();
    clear_pmp!();
}

/// Physical memory protection configuration
/// pmpcfg1 struct contains pmp4cfg - pmp7cfg for RV32 only
#[cfg(target_arch = "riscv32")]
pub mod pmpcfg1 {
    use super::{Permission, Pmpcsr, Range};

    read_csr_as!(Pmpcsr, 0x3A1);
    write_csr_as_usize_rv32!(0x3A1);

    set_pmp!();
    clear_pmp!();
}

/// Physical memory protection configuration
/// pmpcfg2 struct contains pmp8cfg - pmp11cfg for RV32, or pmp8cfg - pmp15cfg for RV64
pub mod pmpcfg2 {
    use super::{Permission, Pmpcsr, Range};

    read_csr_as!(Pmpcsr, 0x3A2);
    write_csr_as_usize!(0x3A2);

    set_pmp!();
    clear_pmp!();
}

/// Physical memory protection configuration
/// pmpcfg3 struct contains pmp12cfg - pmp15cfg for RV32 only
#[cfg(target_arch = "riscv32")]
pub mod pmpcfg3 {
    use super::{Permission, Pmpcsr, Range};

    read_csr_as!(Pmpcsr, 0x3A3);
    write_csr_as_usize_rv32!(0x3A3);

    set_pmp!();
    clear_pmp!();
}

/// Physical memory protection configuration
/// pmpcfg4 struct contains pmp16cfg - pmp19cfg for RV32, or pmp16cfg - pmp23cfg for RV64
pub mod pmpcfg4 {
    use super::{Permission, Pmpcsr, Range};

    read_csr_as!(Pmpcsr, 0x3A4);
    write_csr_as_usize!(0x3A4);

    set_pmp!();
    clear_pmp!();
}

/// Physical memory protection configuration
/// pmpcfg5 struct contains pmp20cfg - pmp23cfg for RV32 only
#[cfg(target_arch = "riscv32")]
pub mod pmpcfg5 {
    use super::{Permission, Pmpcsr, Range};

    read_csr_as!(Pmpcsr, 0x3A5);
    write_csr_as_usize_rv32!(0x3A5);

    set_pmp!();
    clear_pmp!();
}

/// Physical memory protection configuration
/// pmpcfg6 struct contains pmp24cfg - pmp27cfg for RV32, or pmp24cfg - pmp31cfg for RV64
pub mod pmpcfg6 {
    use super::{Permission, Pmpcsr, Range};

    read_csr_as!(Pmpcsr, 0x3A6);
    write_csr_as_usize!(0x3A6);

    set_pmp!();
    clear_pmp!();
}

/// Physical memory protection configuration
/// pmpcfg7 struct contains pmp28cfg - pmp31cfg for RV32 only
#[cfg(target_arch = "riscv32")]
pub mod pmpcfg7 {
    use super::{Permission, Pmpcsr, Range};

    read_csr_as!(Pmpcsr, 0x3A7);
    write_csr_as_usize_rv32!(0x3A7);

    set_pmp!();
    clear_pmp!();
}

/// Physical memory protection configuration
/// pmpcfg8 struct contains pmp32cfg - pmp35cfg for RV32, or pmp32cfg - pmp39cfg for RV64
pub mod pmpcfg8 {
    use super::{Permission, Pmpcsr, Range};

    read_csr_as!(Pmpcsr, 0x3A8);
    write_csr_as_usize!(0x3A8);

    set_pmp!();
    clear_pmp!();
}

/// Physical memory protection configuration
/// pmpcfg9 struct contains pmp36cfg - pmp39cfg for RV32 only
#[cfg(target_arch = "riscv32")]
pub mod pmpcfg9 {
    use super::{Permission, Pmpcsr, Range};

    read_csr_as!(Pmpcsr, 0x3A9);
    write_csr_as_usize_rv32!(0x3A9);

    set_pmp!();
    clear_pmp!();
}

/// Physical memory protection configuration
/// pmpcfg10 struct contains pmp40cfg - pmp43cfg for RV32, or pmp40cfg - pmp47cfg for RV64
pub mod pmpcfg10 {
    use super::{Permission, Pmpcsr, Range};

    read_csr_as!(Pmpcsr, 0x3AA);
    write_csr_as_usize!(0x3AA);

    set_pmp!();
    clear_pmp!();
}

/// Physical memory protection configuration
/// pmpcfg11 struct contains pmp44cfg - pmp47cfg for RV32 only
#[cfg(target_arch = "riscv32")]
pub mod pmpcfg11 {
    use super::{Permission, Pmpcsr, Range};

    read_csr_as!(Pmpcsr, 0x3AB);
    write_csr_as_usize_rv32!(0x3AB);

    set_pmp!();
    clear_pmp!();
}

/// Physical memory protection configuration
/// pmpcfg12 struct contains pmp48cfg - pmp51cfg for RV32, or pmp48cfg - pmp55cfg for RV64
pub mod pmpcfg12 {
    use super::{Permission, Pmpcsr, Range};

    read_csr_as!(Pmpcsr, 0x3AC);
    write_csr_as_usize!(0x3AC);

    set_pmp!();
    clear_pmp!();
}

/// Physical memory protection configuration
/// pmpcfg13 struct contains pmp52cfg - pmp55cfg for RV32 only
#[cfg(target_arch = "riscv32")]
pub mod pmpcfg13 {
    use super::{Permission, Pmpcsr, Range};

    read_csr_as!(Pmpcsr, 0x3AD);
    write_csr_as_usize_rv32!(0x3AD);

    set_pmp!();
    clear_pmp!();
}

/// Physical memory protection configuration
/// pmpcfg14 struct contains pmp56cfg - pmp59cfg for RV32, or pmp56cfg - pmp63cfg for RV64
pub mod pmpcfg14 {
    use super::{Permission, Pmpcsr, Range};

    read_csr_as!(Pmpcsr, 0x3AE);
    write_csr_as_usize!(0x3AE);

    set_pmp!();
    clear_pmp!();
}

/// Physical memory protection configuration
/// pmpcfg15 struct contains pmp60cfg - pmp63cfg for RV32 only
#[cfg(target_arch = "riscv32")]
pub mod pmpcfg15 {
    use super::{Permission, Pmpcsr, Range};

    read_csr_as!(Pmpcsr, 0x3AF);
    write_csr_as_usize_rv32!(0x3AF);

    set_pmp!();
    clear_pmp!();
}
