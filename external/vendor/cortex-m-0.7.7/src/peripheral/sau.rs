//! Security Attribution Unit
//!
//! *NOTE* Available only on Armv8-M and Armv8.1-M, for the following Rust target triples:
//!   * `thumbv8m.base-none-eabi`
//!   * `thumbv8m.main-none-eabi`
//!   * `thumbv8m.main-none-eabihf`
//!
//! For reference please check the section B8.3 of the Armv8-M Architecture Reference Manual.

use crate::interrupt;
use crate::peripheral::SAU;
use bitfield::bitfield;
use volatile_register::{RO, RW};

/// Register block
#[repr(C)]
pub struct RegisterBlock {
    /// Control Register
    pub ctrl: RW<Ctrl>,
    /// Type Register
    pub _type: RO<Type>,
    /// Region Number Register
    pub rnr: RW<Rnr>,
    /// Region Base Address Register
    pub rbar: RW<Rbar>,
    /// Region Limit Address Register
    pub rlar: RW<Rlar>,
    /// Secure Fault Status Register
    pub sfsr: RO<Sfsr>,
    /// Secure Fault Address Register
    pub sfar: RO<Sfar>,
}

bitfield! {
    /// Control Register description
    #[repr(C)]
    #[derive(Copy, Clone)]
    pub struct Ctrl(u32);
    get_enable, set_enable: 0;
    get_allns, set_allns: 1;
}

bitfield! {
    /// Type Register description
    #[repr(C)]
    #[derive(Copy, Clone)]
    pub struct Type(u32);
    u8;
    sregion, _: 7, 0;
}

bitfield! {
    /// Region Number Register description
    #[repr(C)]
    #[derive(Copy, Clone)]
    pub struct Rnr(u32);
    u8;
    get_region, set_region: 7, 0;
}

bitfield! {
    /// Region Base Address Register description
    #[repr(C)]
    #[derive(Copy, Clone)]
    pub struct Rbar(u32);
    u32;
    get_baddr, set_baddr: 31, 5;
}

bitfield! {
    /// Region Limit Address Register description
    #[repr(C)]
    #[derive(Copy, Clone)]
    pub struct Rlar(u32);
    u32;
    get_laddr, set_laddr: 31, 5;
    get_nsc, set_nsc: 1;
    get_enable, set_enable: 0;
}

bitfield! {
    /// Secure Fault Status Register description
    #[repr(C)]
    #[derive(Copy, Clone)]
    pub struct Sfsr(u32);
    invep, _: 0;
    invis, _: 1;
    inver, _: 2;
    auviol, _: 3;
    invtran, _: 4;
    lsperr, _: 5;
    sfarvalid, _: 6;
    lserr, _: 7;
}

bitfield! {
    /// Secure Fault Address Register description
    #[repr(C)]
    #[derive(Copy, Clone)]
    pub struct Sfar(u32);
    u32;
    address, _: 31, 0;
}

/// Possible attribute of a SAU region.
#[derive(Debug)]
pub enum SauRegionAttribute {
    /// SAU region is Secure
    Secure,
    /// SAU region is Non-Secure Callable
    NonSecureCallable,
    /// SAU region is Non-Secure
    NonSecure,
}

/// Description of a SAU region.
#[derive(Debug)]
pub struct SauRegion {
    /// First address of the region, its 5 least significant bits must be set to zero.
    pub base_address: u32,
    /// Last address of the region, its 5 least significant bits must be set to one.
    pub limit_address: u32,
    /// Attribute of the region.
    pub attribute: SauRegionAttribute,
}

/// Possible error values returned by the SAU methods.
#[derive(Debug)]
pub enum SauError {
    /// The region number parameter to set or get a region must be between 0 and
    /// region_numbers() - 1.
    RegionNumberTooBig,
    /// Bits 0 to 4 of the base address of a SAU region must be set to zero.
    WrongBaseAddress,
    /// Bits 0 to 4 of the limit address of a SAU region must be set to one.
    WrongLimitAddress,
}

impl SAU {
    /// Get the number of implemented SAU regions.
    #[inline]
    pub fn region_numbers(&self) -> u8 {
        self._type.read().sregion()
    }

    /// Enable the SAU.
    #[inline]
    pub fn enable(&mut self) {
        unsafe {
            self.ctrl.modify(|mut ctrl| {
                ctrl.set_enable(true);
                ctrl
            });
        }
    }

    /// Set a SAU region to a region number.
    /// SAU regions must be 32 bytes aligned and their sizes must be a multiple of 32 bytes. It
    /// means that the 5 least significant bits of the base address of a SAU region must be set to
    /// zero and the 5 least significant bits of the limit address must be set to one.
    /// The region number must be valid.
    /// This function is executed under a critical section to prevent having inconsistent results.
    #[inline]
    pub fn set_region(&mut self, region_number: u8, region: SauRegion) -> Result<(), SauError> {
        interrupt::free(|_| {
            let base_address = region.base_address;
            let limit_address = region.limit_address;
            let attribute = region.attribute;

            if region_number >= self.region_numbers() {
                Err(SauError::RegionNumberTooBig)
            } else if base_address & 0x1F != 0 {
                Err(SauError::WrongBaseAddress)
            } else if limit_address & 0x1F != 0x1F {
                Err(SauError::WrongLimitAddress)
            } else {
                // All fields of these registers are going to be modified so we don't need to read them
                // before.
                let mut rnr = Rnr(0);
                let mut rbar = Rbar(0);
                let mut rlar = Rlar(0);

                rnr.set_region(region_number);
                rbar.set_baddr(base_address >> 5);
                rlar.set_laddr(limit_address >> 5);

                match attribute {
                    SauRegionAttribute::Secure => {
                        rlar.set_nsc(false);
                        rlar.set_enable(false);
                    }
                    SauRegionAttribute::NonSecureCallable => {
                        rlar.set_nsc(true);
                        rlar.set_enable(true);
                    }
                    SauRegionAttribute::NonSecure => {
                        rlar.set_nsc(false);
                        rlar.set_enable(true);
                    }
                }

                unsafe {
                    self.rnr.write(rnr);
                    self.rbar.write(rbar);
                    self.rlar.write(rlar);
                }

                Ok(())
            }
        })
    }

    /// Get a region from the SAU.
    /// The region number must be valid.
    /// This function is executed under a critical section to prevent having inconsistent results.
    #[inline]
    pub fn get_region(&mut self, region_number: u8) -> Result<SauRegion, SauError> {
        interrupt::free(|_| {
            if region_number >= self.region_numbers() {
                Err(SauError::RegionNumberTooBig)
            } else {
                unsafe {
                    self.rnr.write(Rnr(region_number.into()));
                }

                let rbar = self.rbar.read();
                let rlar = self.rlar.read();

                let attribute = match (rlar.get_enable(), rlar.get_nsc()) {
                    (false, _) => SauRegionAttribute::Secure,
                    (true, false) => SauRegionAttribute::NonSecure,
                    (true, true) => SauRegionAttribute::NonSecureCallable,
                };

                Ok(SauRegion {
                    base_address: rbar.get_baddr() << 5,
                    limit_address: (rlar.get_laddr() << 5) | 0x1F,
                    attribute,
                })
            }
        })
    }
}
