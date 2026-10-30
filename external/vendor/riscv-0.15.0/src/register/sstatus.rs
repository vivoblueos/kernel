//! sstatus register

pub use super::misa::XLEN;
pub use super::mstatus::{FS, XS};

#[cfg(target_arch = "riscv32")]
const MASK: usize = 0x800d_e122;
#[cfg(not(target_arch = "riscv32"))]
const MASK: usize = 0x8000_0003_000d_e122;

read_write_csr! {
    /// Supervisor Status Register
    Sstatus: 0x100,
    mask: MASK,
}

csr_field_enum! {
    /// Supervisor Previous Privilege Mode
    SPP {
        default: User,
        /// Previous privilege mode is User mode.
        User = 0,
        /// Previous privilege mode is Supervisor mode.
        Supervisor = 1,
    }
}

read_write_csr_field! {
    Sstatus,
    /// Supervisor Interrupt Enable
    sie: 1,
}

read_write_csr_field! {
    Sstatus,
    /// Supervisor Previous Interrupt Enable
    spie: 5,
}

read_write_csr_field! {
    Sstatus,
    /// Supervisor Previous Privilege Mode
    spp,
    SPP: [8:8],
}

read_write_csr_field! {
    Sstatus,
    /// The status of the floating-point unit
    fs,
    FS: [13:14],
}

read_only_csr_field! {
    Sstatus,
    /// The status of additional user-mode extensions
    /// and associated state
    xs,
    XS: [15:16],
}

read_write_csr_field! {
    Sstatus,
    /// Permit Supervisor User Memory access
    sum: 18,
}

read_write_csr_field! {
    Sstatus,
    /// Make eXecutable Readable
    mxr: 19,
}

#[cfg(not(target_arch = "riscv32"))]
read_write_csr_field! {
    Sstatus,
    /// Effective xlen in U-mode (i.e., `UXLEN`).
    uxl,
    XLEN: [32:33],
}

#[cfg(target_arch = "riscv32")]
read_write_csr_field! {
    Sstatus,
    /// Whether either the FS field or XS field
    /// signals the presence of some dirty state
    sd: 31,
}

#[cfg(not(target_arch = "riscv32"))]
read_write_csr_field! {
    Sstatus,
    /// Whether either the FS field or XS field
    /// signals the presence of some dirty state
    sd: 63,
}

impl Sstatus {
    /// Effective xlen in U-mode (i.e., `UXLEN`).
    ///
    /// In RISCV-32, UXL does not exist, and `UXLEN` is always [`XLEN::XLEN32`].
    #[inline]
    #[cfg(target_arch = "riscv32")]
    pub fn uxl(&self) -> XLEN {
        XLEN::XLEN32
    }
}

set!(0x100);
clear!(0x100);

set_clear_csr!(
    /// User Interrupt Enable
    , set_uie, clear_uie, 1 << 0);
set_clear_csr!(
    /// Supervisor Interrupt Enable
    , set_sie, clear_sie, 1 << 1);
set_csr!(
    /// User Previous Interrupt Enable
    , set_upie, 1 << 4);
set_csr!(
    /// Supervisor Previous Interrupt Enable
    , set_spie, 1 << 5);
set_clear_csr!(
    /// Permit Supervisor User Memory access
    , set_sum, clear_sum, 1 << 18);
set_clear_csr!(
    /// Make eXecutable Readable
    , set_mxr, clear_mxr, 1 << 19);

/// Supervisor Previous Privilege Mode
#[inline]
pub unsafe fn set_spp(spp: SPP) {
    match spp {
        SPP::Supervisor => _set(1 << 8),
        SPP::User => _clear(1 << 8),
    }
}

/// The status of the floating-point unit
#[inline]
pub unsafe fn set_fs(fs: FS) {
    let mut value = _read();
    value &= !(0x3 << 13); // clear previous value
    value |= (fs as usize) << 13;
    _write(value);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sstatus() {
        let mut sstatus = Sstatus::from_bits(0);

        test_csr_field!(sstatus, sie);
        test_csr_field!(sstatus, spie);

        [SPP::User, SPP::Supervisor].into_iter().for_each(|spp| {
            test_csr_field!(sstatus, spp: spp);
        });

        [FS::Off, FS::Initial, FS::Clean, FS::Dirty]
            .into_iter()
            .for_each(|fs| {
                test_csr_field!(sstatus, fs: fs);
            });

        [
            XS::AllOff,
            XS::NoneDirtyOrClean,
            XS::NoneDirtySomeClean,
            XS::SomeDirty,
        ]
        .into_iter()
        .for_each(|xs| {
            let sstatus = Sstatus::from_bits(xs.into_usize() << 15);
            assert_eq!(sstatus.xs(), xs);
            assert_eq!(sstatus.try_xs(), Ok(xs));
        });

        test_csr_field!(sstatus, sum);
        test_csr_field!(sstatus, mxr);

        [XLEN::XLEN32, XLEN::XLEN64, XLEN::XLEN128]
            .into_iter()
            .for_each(|xlen| {
                test_csr_field!(sstatus, uxl: xlen);
            });

        test_csr_field!(sstatus, sd);
    }
}
