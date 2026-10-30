//! mstatus register

pub use super::misa::XLEN;
#[cfg(not(target_arch = "riscv32"))]
use crate::bits::{bf_extract, bf_insert};

#[cfg(not(target_arch = "riscv32"))]
read_write_csr! {
    /// mstatus register
    Mstatus: 0x300,
    mask: 0x8000_0000_007f_fffe,
}

#[cfg(target_arch = "riscv32")]
read_write_csr! {
    /// mstatus register
    Mstatus: 0x300,
    mask: 0x807f_fffe,
}

csr_field_enum! {
    /// Additional extension state
    XS {
        default: AllOff,
        /// All off
        AllOff = 0,
        /// None dirty or clean, some on
        NoneDirtyOrClean = 1,
        /// None dirty, some clean
        NoneDirtySomeClean = 2,
        /// Some dirty
        SomeDirty = 3,
    }
}

csr_field_enum! {
    /// Floating-point extension state
    FS {
        default: Off,
        Off = 0,
        Initial = 1,
        Clean = 2,
        Dirty = 3,
    }
}

csr_field_enum! {
    /// Vector extension state
    VS {
        default: Off,
        Off = 0,
        Initial = 1,
        Clean = 2,
        Dirty = 3,
    }
}

csr_field_enum! {
    /// Machine Previous Privilege Mode
    MPP {
        default: User,
        User = 0,
        Supervisor = 1,
        Machine = 3,
    }
}

csr_field_enum! {
    /// Supervisor Previous Privilege Mode
    SPP {
        default: User,
        User = 0,
        Supervisor = 1,
    }
}

csr_field_enum! {
    /// Non-instruction-fetch memory endianness
    Endianness {
        default: LittleEndian,
        LittleEndian = 0,
        BigEndian = 1,
    }
}

impl From<bool> for Endianness {
    fn from(val: bool) -> Self {
        match val {
            false => Self::LittleEndian,
            true => Self::BigEndian,
        }
    }
}

read_write_csr_field! {
    Mstatus,
    /// Supervisor Interrupt Enable
    sie: 1,
}

read_write_csr_field! {
    Mstatus,
    /// Machine Interrupt Enable
    mie: 3,
}

read_write_csr_field! {
    Mstatus,
    /// Supervisor Previous Interrupt Enable
    spie: 5,
}

read_write_csr_field! {
    Mstatus,
    /// U-mode non-instruction-fetch memory endianness
    ube: 6,
}

read_write_csr_field! {
    Mstatus,
    /// Machine Previous Interrupt Enable
    mpie: 7,
}

read_write_csr_field! {
    Mstatus,
    /// Supervisor Previous Privilege Mode
    spp,
    SPP: [8:8],
}

read_write_csr_field! {
    Mstatus,
    /// Vector extension state
    vs,
    VS: [9:10],
}

read_write_csr_field! {
    Mstatus,
    /// Machine Previous Privilege Mode
    mpp,
    MPP: [11:12],
}

read_write_csr_field! {
    Mstatus,
    /// Floating-point extension state
    ///
    /// Encodes the status of the floating-point unit, including the CSR `fcsr`
    /// and floating-point data registers `f0–f31`.
    fs,
    FS: [13:14],
}

read_write_csr_field! {
    Mstatus,
    /// Additional extension state
    ///
    /// Encodes the status of additional user-mode extensions and associated
    /// state.
    xs,
    XS: [15:16],
}

read_write_csr_field! {
    Mstatus,
    /// Modify Memory PRiVilege
    mprv: 17,
}

read_write_csr_field! {
    Mstatus,
    /// Permit Supervisor User Memory access
    sum: 18,
}

read_write_csr_field! {
    Mstatus,
    /// Make eXecutable Readable
    mxr: 19,
}

read_write_csr_field! {
    Mstatus,
    /// Trap Virtual Memory
    ///
    /// If this bit is set, reads or writes to `satp` CSR or execute `sfence.vma`
    /// instruction when in S-mode will raise an illegal instruction exception.
    ///
    /// TVM is hard-wired to 0 when S-mode is not supported.
    tvm: 20,
}

read_write_csr_field! {
    Mstatus,
    /// Timeout Wait
    ///
    /// Indicates that if WFI instruction should be intercepted.
    ///
    /// If this bit is set, when WFI is executed in S-mode, and it does not complete
    /// within an implementation specific, bounded time limit, the WFI instruction will cause
    /// an illegal instruction trap; or could always cause trap then the time limit is zero.
    ///
    /// TW is hard-wired to 0 when S-mode is not supported.
    tw: 21,
}

read_write_csr_field! {
    Mstatus,
    /// Trap SRET
    ///
    /// Indicates that if SRET instruction should be trapped to raise illegal
    /// instruction exception.
    ///
    /// If S-mode is not supported, TSR bit is hard-wired to 0.
    tsr: 22,
}

#[cfg(target_arch = "riscv32")]
read_write_csr_field! {
    Mstatus,
    /// Whether either the FS field or XS field signals the presence of some dirty state
    sd: 31,
}

#[cfg(not(target_arch = "riscv32"))]
read_write_csr_field! {
    Mstatus,
    /// Whether either the FS field or XS field signals the presence of some dirty state
    sd: 63,
}

impl Mstatus {
    /// Effective xlen in U-mode (i.e., `UXLEN`).
    ///
    /// In RISCV-32, UXL does not exist, and `UXLEN` is always [`XLEN::XLEN32`].
    #[inline]
    pub fn uxl(&self) -> XLEN {
        match () {
            #[cfg(not(target_arch = "riscv32"))]
            () => XLEN::try_from(bf_extract(self.bits, 32, 2)).unwrap_or_default(),
            #[cfg(target_arch = "riscv32")]
            () => XLEN::XLEN32,
        }
    }

    /// Update Effective xlen in U-mode (i.e., `UXLEN`).
    ///
    /// Note this updates a previously read [`Mstatus`] value, but does not
    /// affect the mstatus CSR itself.
    ///
    /// # Note
    ///
    /// In RISCV-32, `UXL` does not exist, and `UXLEN` is always [`XLEN::XLEN32`].
    #[inline]
    #[cfg(not(target_arch = "riscv32"))]
    pub fn set_uxl(&mut self, uxl: XLEN) {
        self.bits = bf_insert(self.bits, 32, 2, uxl as usize);
    }

    /// Effective xlen in S-mode (i.e., `SXLEN`).
    ///
    /// In RISCV-32, SXL does not exist, and SXLEN is always [`XLEN::XLEN32`].
    #[inline]
    pub fn sxl(&self) -> XLEN {
        match () {
            #[cfg(target_arch = "riscv32")]
            () => XLEN::XLEN32,
            #[cfg(not(target_arch = "riscv32"))]
            () => XLEN::try_from(bf_extract(self.bits, 34, 2)).unwrap_or_default(),
        }
    }

    /// Update Effective xlen in S-mode (i.e., `SXLEN`).
    ///
    /// Note this updates a previously read [`Mstatus`] value, but does not
    /// affect the mstatus CSR itself.
    ///
    /// # Note
    ///
    /// In RISCV-32, `SXL` does not exist, and `SXLEN` is always [`XLEN::XLEN32`].
    #[inline]
    #[cfg(not(target_arch = "riscv32"))]
    pub fn set_sxl(&mut self, sxl: XLEN) {
        self.bits = bf_insert(self.bits, 34, 2, sxl as usize);
    }

    /// S-mode non-instruction-fetch memory endianness.
    ///
    /// In RISCV-32, this field is read from the [`crate::register::mstatush`] register.
    pub fn sbe(&self) -> Endianness {
        match () {
            #[cfg(not(target_arch = "riscv32"))]
            () => Endianness::from(bf_extract(self.bits, 36, 1) != 0),
            #[cfg(target_arch = "riscv32")]
            () => super::mstatush::read().sbe(),
        }
    }

    /// Update S-mode non-instruction-fetch memory endianness
    ///
    /// Note this updates a previously read [`Mstatus`] value, but does not
    /// affect the mstatus CSR itself. See [`set_sbe`] to directly update the
    /// CSR.
    ///
    /// # Note
    ///
    /// On RISCV-32 platforms, this function does not exist on the [`Mstatus`] instance.
    ///
    /// Instead, RISCV-32 users should use the [`Mstatush`](crate::register::mstatush::Mstatush) register.
    #[inline]
    #[cfg(not(target_arch = "riscv32"))]
    pub fn set_sbe(&mut self, endianness: Endianness) {
        self.bits = bf_insert(self.bits, 36, 1, endianness as usize);
    }

    /// M-mode non-instruction-fetch memory endianness
    ///
    /// In RISCV-32, this field is read from the [`crate::register::mstatush`] register
    pub fn mbe(&self) -> Endianness {
        match () {
            #[cfg(not(target_arch = "riscv32"))]
            () => Endianness::try_from(bf_extract(self.bits, 37, 1)).unwrap_or_default(),
            #[cfg(target_arch = "riscv32")]
            () => super::mstatush::read().mbe(),
        }
    }

    /// Update M-mode non-instruction-fetch memory endianness
    ///
    /// Note this updates a previously read [`Mstatus`] value, but does not
    /// affect the mstatus CSR itself. See [`set_mbe`] to directly update the
    /// CSR.
    ///
    /// # Note
    ///
    /// On RISCV-32 platforms, this function does not exist on the [`Mstatus`] instance.
    ///
    /// Instead, RISCV-32 users should use the [`Mstatush`](crate::register::mstatush::Mstatush) register.
    #[inline]
    #[cfg(not(target_arch = "riscv32"))]
    pub fn set_mbe(&mut self, endianness: Endianness) {
        self.bits = bf_insert(self.bits, 37, 1, endianness as usize);
    }
}

set!(0x300);
clear!(0x300);

set_clear_csr!(
    /// User Interrupt Enable
    , set_uie, clear_uie, 1 << 0);
set_clear_csr!(
    /// Supervisor Interrupt Enable
    , set_sie, clear_sie, 1 << 1);
set_clear_csr!(
    /// Machine Interrupt Enable
    , set_mie, clear_mie, 1 << 3);
set_csr!(
    /// User Previous Interrupt Enable
    , set_upie, 1 << 4);
set_csr!(
    /// Supervisor Previous Interrupt Enable
    , set_spie, 1 << 5);
set_csr!(
    /// Machine Previous Interrupt Enable
    , set_mpie, 1 << 7);
set_clear_csr!(
    /// Modify Memory PRiVilege
    , set_mprv, clear_mprv, 1 << 17);
set_clear_csr!(
    /// Permit Supervisor User Memory access
    , set_sum, clear_sum, 1 << 18);
set_clear_csr!(
    /// Make eXecutable Readable
    , set_mxr, clear_mxr, 1 << 19);
set_clear_csr!(
    /// Trap Virtual Memory
    , set_tvm, clear_tvm, 1 << 20);
set_clear_csr!(
    /// Timeout Wait
    , set_tw, clear_tw, 1 << 21);
set_clear_csr!(
    /// Trap SRET
    , set_tsr, clear_tsr, 1 << 22);

/// Set U-mode non-instruction-fetch memory endianness
#[inline]
pub unsafe fn set_ube(endianness: Endianness) {
    match endianness {
        Endianness::BigEndian => _set(1 << 6),
        Endianness::LittleEndian => _clear(1 << 6),
    }
}

/// Supervisor Previous Privilege Mode
#[inline]
pub unsafe fn set_spp(spp: SPP) {
    match spp {
        SPP::Supervisor => _set(1 << 8),
        SPP::User => _clear(1 << 8),
    }
}

/// Machine Previous Privilege Mode
#[inline]
pub unsafe fn set_mpp(mpp: MPP) {
    let mut value = _read();
    value &= !(0x3 << 11); // clear previous value
    value |= (mpp as usize) << 11;
    _write(value);
}

/// Floating-point extension state
#[inline]
pub unsafe fn set_fs(fs: FS) {
    let mut value = _read();
    value &= !(0x3 << 13); // clear previous value
    value |= (fs as usize) << 13;
    _write(value);
}

/// Vector extension state
#[inline]
pub unsafe fn set_vs(vs: VS) {
    let mut value = _read();
    value &= !(0x3 << 9); // clear previous value
    value |= (vs as usize) << 9;
    _write(value);
}

/// Set S-mode non-instruction-fetch memory endianness
///
/// # Note
///
/// In RISCV-32, this function calls [`crate::register::mstatush::set_sbe`]
#[inline]
pub unsafe fn set_sbe(endianness: Endianness) {
    match () {
        #[cfg(target_arch = "riscv32")]
        () => super::mstatush::set_sbe(endianness),
        #[cfg(not(target_arch = "riscv32"))]
        () => match endianness {
            Endianness::BigEndian => _set(1 << 36),
            Endianness::LittleEndian => _clear(1 << 36),
        },
    }
}

/// Set M-mode non-instruction-fetch memory endianness
///
/// # Note
///
/// In RISCV-32, this function calls [`crate::register::mstatush::set_mbe`]
#[inline]
pub unsafe fn set_mbe(endianness: Endianness) {
    match () {
        #[cfg(target_arch = "riscv32")]
        () => super::mstatush::set_mbe(endianness),
        #[cfg(not(target_arch = "riscv32"))]
        () => match endianness {
            Endianness::BigEndian => _set(1 << 37),
            Endianness::LittleEndian => _clear(1 << 37),
        },
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_mstatus() {
        let mut mstatus = Mstatus { bits: 0 };

        test_csr_field!(mstatus, mpp: MPP::User);
        test_csr_field!(mstatus, mpp: MPP::Machine);
        test_csr_field!(mstatus, mpp: MPP::Supervisor);

        test_csr_field!(mstatus, spp: SPP::User);
        test_csr_field!(mstatus, spp: SPP::Supervisor);

        test_csr_field!(mstatus, fs: FS::Off);
        test_csr_field!(mstatus, fs: FS::Initial);
        test_csr_field!(mstatus, fs: FS::Clean);
        test_csr_field!(mstatus, fs: FS::Dirty);

        test_csr_field!(mstatus, vs: VS::Off);
        test_csr_field!(mstatus, vs: VS::Initial);
        test_csr_field!(mstatus, vs: VS::Clean);
        test_csr_field!(mstatus, vs: VS::Dirty);

        test_csr_field!(mstatus, xs: XS::AllOff);
        test_csr_field!(mstatus, xs: XS::NoneDirtyOrClean);
        test_csr_field!(mstatus, xs: XS::NoneDirtySomeClean);
        test_csr_field!(mstatus, xs: XS::SomeDirty);

        test_csr_field!(mstatus, sie);
        test_csr_field!(mstatus, mie);
        test_csr_field!(mstatus, spie);
        test_csr_field!(mstatus, ube);
        test_csr_field!(mstatus, mpie);
        test_csr_field!(mstatus, mprv);
        test_csr_field!(mstatus, sum);
        test_csr_field!(mstatus, mxr);
        test_csr_field!(mstatus, tvm);
        test_csr_field!(mstatus, tw);
        test_csr_field!(mstatus, tsr);
        test_csr_field!(mstatus, sd);
    }
}
