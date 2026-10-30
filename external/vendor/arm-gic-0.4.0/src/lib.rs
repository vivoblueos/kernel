// Copyright 2023 The arm-gic Authors.
// This project is dual-licensed under Apache 2.0 and MIT terms.
// See LICENSE-APACHE and LICENSE-MIT for details.

//! Driver for the Arm Generic Interrupt Controller version 2, 3 or 4, on aarch64.
//!
//! This top level module contains functions that are not specific to any particular interrupt
//! controller, as support for other GIC versions may be added in future.
//!
//! # Example
//!
//! Using a GICv3 on a single-core aarch64 system:
//!
//! ```
//! use arm_gic::{
//!     gicv3::{GicV3, SgiTarget},
//!     irq_enable, IntId,
//! };
//!
//! // Base addresses of the GICv3 distributor and redistributor.
//! const GICD_BASE_ADDRESS: *mut u64 = 0x800_0000 as _;
//! const GICR_BASE_ADDRESS: *mut u64 = 0x80A_0000 as _;
//!
//! // Initialise the GIC.
//! let mut gic = unsafe { GicV3::new(GICD_BASE_ADDRESS, GICR_BASE_ADDRESS, 1, 0x20000) };
//! gic.setup(0);
//!
//! // Configure an SGI and then send it to ourself.
//! let sgi_intid = IntId::sgi(3);
//! SingleCoreGicV3::set_priority_mask(0xff);
//! gic.set_interrupt_priority(sgi_intid, Some(0), 0x80);
//! gic.enable_interrupt(sgi_intid, Some(0), true);
//! irq_enable();
//! SingleCoreGicV3::send_sgi(
//!     sgi_intid,
//!     SgiTarget::List {
//!         affinity3: 0,
//!         affinity2: 0,
//!         affinity1: 0,
//!         target_list: 0b1,
//!     },
//! );
//! ```

#![cfg_attr(not(any(test, feature = "fakes")), no_std)]
#![deny(clippy::undocumented_unsafe_blocks)]

pub mod gicv2;
pub mod gicv3;
mod sysreg;

#[cfg(feature = "fakes")]
pub use sysreg::fake as sysreg_fake;

#[cfg(target_arch = "aarch64")]
use core::arch::asm;
use core::fmt::{Debug, Formatter, Result};

/// The trigger configuration for an interrupt.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Trigger {
    /// The interrupt is edge triggered.
    Edge,
    /// The interrupt is level triggered.
    Level,
}

/// An interrupt ID.
#[derive(Copy, Clone, Eq, Ord, PartialOrd, PartialEq)]
pub struct IntId(u32);

impl IntId {
    /// Special interrupt ID returned when running at EL3 and the interrupt should be handled at
    /// S-EL2 or S-EL1.
    pub const SPECIAL_SECURE: Self = Self(1020);

    /// Special interrupt ID returned when running at EL3 and the interrupt should be handled at
    /// (non-secure) EL2 or EL1.
    pub const SPECIAL_NONSECURE: Self = Self(1021);

    /// Special interrupt ID returned when the interrupt is a non-maskable interrupt.
    pub const SPECIAL_NMI: Self = Self(1022);

    /// Special interrupt ID returned when there is no pending interrupt of sufficient priority for
    /// the current security state and interrupt group.
    pub const SPECIAL_NONE: Self = Self(1023);

    /// The maximum number of SPIs which may be supported.
    pub const MAX_SPI_COUNT: u32 = Self::SPECIAL_START - Self::SPI_START;

    /// The number of Software Generated Interrupts.
    pub const SGI_COUNT: u32 = Self::PPI_START - Self::SGI_START;

    /// The number of (non-extended) Private Peripheral Interrupts.
    pub const PPI_COUNT: u32 = Self::SPI_START - Self::PPI_START;

    /// The maximum number of extended Private Peripheral Interrupts which may be supported.
    pub const MAX_EPPI_COUNT: u32 = Self::EPPI_END - Self::EPPI_START;

    /// The maximum number of extended Shared Peripheral Interrupts which may be supported.
    pub const MAX_ESPI_COUNT: u32 = Self::ESPI_END - Self::ESPI_START;

    /// The ID of the first Software Generated Interrupt.
    const SGI_START: u32 = 0;

    /// The ID of the first Private Peripheral Interrupt.
    const PPI_START: u32 = 16;

    /// The ID of the first Shared Peripheral Interrupt.
    const SPI_START: u32 = 32;

    /// The first special interrupt ID.
    const SPECIAL_START: u32 = 1020;

    /// One more than the last special interrupt ID.
    const SPECIAL_END: u32 = 1024;

    /// The first extended Private Peripheral Interrupt.
    const EPPI_START: u32 = 1056;

    /// One more than the last extended Private Peripheral Interrupt.
    const EPPI_END: u32 = 1120;

    /// The first extended Shared Peripheral Interrupt.
    const ESPI_START: u32 = 4096;

    /// One more than the last extended Shared Peripheral Interrupt.
    const ESPI_END: u32 = 5120;

    /// The first Locality-specific Peripheral Interrupt.
    const LPI_START: u32 = 8192;

    /// Returns the interrupt ID for the given Software Generated Interrupt.
    pub const fn sgi(sgi: u32) -> Self {
        assert!(sgi < Self::SGI_COUNT);
        Self(Self::SGI_START + sgi)
    }

    /// Returns the interrupt ID for the given Private Peripheral Interrupt.
    pub const fn ppi(ppi: u32) -> Self {
        assert!(ppi < Self::PPI_COUNT);
        Self(Self::PPI_START + ppi)
    }

    /// Returns the interrupt ID for the given Shared Peripheral Interrupt.
    pub const fn spi(spi: u32) -> Self {
        assert!(spi < Self::MAX_SPI_COUNT);
        Self(Self::SPI_START + spi)
    }

    /// Returns the interrupt ID for the given extended Private Peripheral Interrupt.
    pub const fn eppi(eppi: u32) -> Self {
        assert!(eppi < Self::MAX_EPPI_COUNT);
        Self(Self::EPPI_START + eppi)
    }

    /// Returns the interrupt ID for the given extended Shared Peripheral Interrupt.
    pub const fn espi(espi: u32) -> Self {
        assert!(espi < Self::MAX_ESPI_COUNT);
        Self(Self::ESPI_START + espi)
    }

    /// Returns the interrupt ID for the given Locality-specific Peripheral Interrupt.
    pub const fn lpi(lpi: u32) -> Self {
        Self(Self::LPI_START + lpi)
    }

    /// Returns whether this interrupt ID is for a Software Generated Interrupt.
    pub const fn is_sgi(self) -> bool {
        self.0 < Self::PPI_START
    }

    /// Returns whether this interrupt ID is for a Private Peripheral Interrupt.
    pub const fn is_ppi(self) -> bool {
        Self::PPI_START <= self.0 && self.0 < Self::SPI_START
    }

    /// Returns whether this interrupt ID is private to a core, i.e. it is an SGI or PPI.
    pub const fn is_private(self) -> bool {
        self.is_sgi() || self.is_ppi()
    }

    /// Returns whether this interrupt ID is for a Shared Peripheral Interrupt.
    pub const fn is_spi(self) -> bool {
        Self::SPI_START <= self.0 && self.0 < Self::SPECIAL_START
    }

    // TODO: Change this to return a Range<IntId> once core::iter::Step is stabilised.
    /// Returns an array of all interrupt Ids that are private to a core, i.e. SGIs and PPIs.
    pub fn private() -> impl Iterator<Item = IntId> {
        let sgis = (0..Self::SGI_COUNT).map(Self::sgi);
        let ppis = (0..Self::PPI_COUNT).map(Self::ppi);

        sgis.chain(ppis)
    }

    // TODO: Change this to return a Range<IntId> once core::iter::Step is stabilised.
    /// Returns an array of all SPI Ids.
    pub fn spis() -> impl Iterator<Item = IntId> {
        (0..Self::MAX_SPI_COUNT).map(Self::spi)
    }
}

impl Debug for IntId {
    fn fmt(&self, f: &mut Formatter) -> Result {
        if self.0 < Self::PPI_START {
            write!(f, "SGI {}", self.0 - Self::SGI_START)
        } else if self.0 < Self::SPI_START {
            write!(f, "PPI {}", self.0 - Self::PPI_START)
        } else if self.0 < Self::SPECIAL_START {
            write!(f, "SPI {}", self.0 - Self::SPI_START)
        } else if self.0 < Self::SPECIAL_END {
            write!(f, "Special IntId {}", self.0)
        } else if self.0 < Self::EPPI_START {
            write!(f, "Reserved IntId {}", self.0)
        } else if self.0 < Self::EPPI_END {
            write!(f, "EPPI {}", self.0 - Self::EPPI_START)
        } else if self.0 < Self::ESPI_START {
            write!(f, "Reserved IntId {}", self.0)
        } else if self.0 < Self::ESPI_END {
            write!(f, "ESPI {}", self.0 - Self::ESPI_START)
        } else if self.0 < Self::LPI_START {
            write!(f, "Reserved IntId {}", self.0)
        } else {
            write!(f, "LPI {}", self.0 - Self::LPI_START)
        }
    }
}

impl From<IntId> for u32 {
    fn from(intid: IntId) -> Self {
        intid.0
    }
}

/// Disables debug, SError, IRQ and FIQ exceptions.
#[cfg(target_arch = "aarch64")]
pub fn irq_disable() {
    // SAFETY: Writing to this system register doesn't access memory in any way.
    unsafe {
        asm!("msr DAIFSet, #0xf", options(nomem, nostack));
    }
}

/// Enables debug, SError, IRQ and FIQ exceptions.
#[cfg(target_arch = "aarch64")]
pub fn irq_enable() {
    // SAFETY: Writing to this system register doesn't access memory in any way.
    unsafe {
        asm!("msr DAIFClr, #0xf", options(nomem, nostack));
    }
}

/// Waits for an interrupt.
#[cfg(target_arch = "aarch64")]
pub fn wfi() {
    // SAFETY: This doesn't access memory in any way.
    unsafe {
        asm!("wfi", options(nomem, nostack));
    }
}
