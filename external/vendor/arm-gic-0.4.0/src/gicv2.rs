// Copyright 2025 The arm-gic Authors.
// This project is dual-licensed under Apache 2.0 and MIT terms.
// See LICENSE-APACHE and LICENSE-MIT for details.

//! Driver for the Arm Generic Interrupt Controller version 2.

pub mod registers;

pub use self::registers::Typer;
use self::registers::{Gicc, Gicd, GicdCtlr};
use crate::{IntId, Trigger};
use core::ptr::NonNull;
use safe_mmio::{field, field_shared, UniqueMmioPointer};

/// Driver for an Arm Generic Interrupt Controller version 2.
#[derive(Debug)]
pub struct GicV2<'a> {
    gicd: UniqueMmioPointer<'a, Gicd>,
    gicc: UniqueMmioPointer<'a, Gicc>,
}

impl GicV2<'_> {
    /// Constructs a new instance of the driver for a GIC with the given distributor and
    /// controller base addresses.
    ///
    /// # Safety
    ///
    /// The given base addresses must point to the GIC distributor and controller registers
    /// respectively. These regions must be mapped into the address space of the process as device
    /// memory, and not have any other aliases, either via another instance of this driver or
    /// otherwise.
    pub unsafe fn new(gicd: *mut Gicd, gicc: *mut Gicc) -> Self {
        Self {
            gicd: UniqueMmioPointer::new(NonNull::new(gicd).unwrap()),
            gicc: UniqueMmioPointer::new(NonNull::new(gicc).unwrap()),
        }
    }

    /// Returns information about what the GIC implementation supports.
    pub fn typer(&self) -> Typer {
        field_shared!(self.gicd, typer).read()
    }

    /// Initialises the GIC.
    pub fn setup(&mut self) {
        field!(self.gicd, ctlr).write(GicdCtlr::EnableGrp1);
        for i in 0..32 {
            field!(self.gicd, igroupr).get(i).unwrap().write(0xffffffff);
        }

        field!(self.gicc, ctlr).write(0b1);
        field!(self.gicc, pmr).write(0xff);
    }

    /// Enables or disables the interrupt with the given ID.
    pub fn enable_interrupt(&mut self, intid: IntId, enable: bool) -> Result<(), ()> {
        let index = (intid.0 / 32) as usize;
        let bit = 1 << (intid.0 % 32);

        if enable {
            field!(self.gicd, isenabler).get(index).unwrap().write(bit);
            if (field_shared!(self.gicd, isenabler)
                .get(index)
                .unwrap()
                .read()
                & bit)
                == 0
            {
                return Err(());
            }
        } else {
            field!(self.gicd, icenabler).get(index).unwrap().write(bit);
        }
        Ok(())
    }

    /// Enables all interrupts.
    pub fn enable_all_interrupts(&mut self, enable: bool) {
        for i in 0..32 {
            if enable {
                field!(self.gicd, isenabler)
                    .get(i)
                    .unwrap()
                    .write(0xffffffff);
            } else {
                field!(self.gicd, icenabler)
                    .get(i)
                    .unwrap()
                    .write(0xffffffff);
            }
        }
    }

    /// Sets the priority mask for the current CPU core.
    ///
    /// Only interrupts with a higher priority (numerically lower) will be signalled.
    pub fn set_priority_mask(&mut self, min_priority: u8) {
        field!(self.gicc, pmr).write(min_priority as u32);
    }

    /// Sets the priority of the interrupt with the given ID.
    ///
    /// Note that lower numbers correspond to higher priorities; i.e. 0 is the highest priority, and
    /// 255 is the lowest.
    pub fn set_interrupt_priority(&mut self, intid: IntId, priority: u8) {
        let idx = intid.0 as usize / 4;
        let priority = (priority as u32) << (8 * (intid.0 % 4));
        field!(self.gicd, ipriorityr)
            .get(idx)
            .unwrap()
            .write(priority);
    }

    /// Configures the trigger type for the interrupt with the given ID.
    pub fn set_trigger(&mut self, intid: IntId, trigger: Trigger) {
        let index = (intid.0 / 16) as usize;
        let bit = 1 << (((intid.0 % 16) * 2) + 1);

        // Affinity routing is not available. So instead use the icfgr register present on all
        // GICD interfaces (present as guaranteed by the user) to set trigger modes.
        let mut icfgr = field!(self.gicd, icfgr);
        let mut register = icfgr.get(index).unwrap();
        let v = register.read();
        register.write(match trigger {
            Trigger::Edge => v | bit,
            Trigger::Level => v & !bit,
        });
    }

    /// Sends a software-generated interrupt (SGI) to the given cores.
    pub fn send_sgi(&mut self, intid: IntId, target: SgiTarget) {
        assert!(intid.is_sgi());

        let sgi_value = match target {
            SgiTarget::All => (intid.0 & 0x0f) | (0xff << 16),
            SgiTarget::List {
                target_list_filter,
                target_list,
            } => {
                (intid.0 & 0xf)
                    | (match target_list_filter {
                        SgiTargetListFilter::CPUTargetList => 0b00,
                        SgiTargetListFilter::ForwardOthersOnly => 0b01,
                        SgiTargetListFilter::ForwardSelfOnly => 0b10,
                    } << 24)
                    | (u32::from(target_list & 0xff) << 16)
                    | (1u32 << 15)
            }
        };

        field!(self.gicd, sgir).write(sgi_value);
    }

    /// Gets the ID of the highest priority signalled interrupt, and acknowledges it.
    ///
    /// Returns `None` if there is no ptending interrupt of sufficient priority.
    pub fn get_and_acknowledge_interrupt(&mut self) -> Option<IntId> {
        let intid = IntId(field!(self.gicc, aiar).read());
        if intid == IntId::SPECIAL_NONE {
            None
        } else {
            Some(intid)
        }
    }

    /// Informs the interrupt controller that the CPU has completed processing the given interrupt.
    /// This drops the interrupt priority and deactivates the interrupt.
    pub fn end_interrupt(&mut self, intid: IntId) {
        field!(self.gicc, aeoir).write(intid.0);
    }
}

/// The target specification for a software-generated interrupt.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum SgiTarget {
    /// The SGI is routed to all CPU cores except the current one.
    All,
    /// The SGI is routed to the CPU cores matching the given affinities and list.
    List {
        target_list_filter: SgiTargetListFilter,
        target_list: u16,
    },
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum SgiTargetListFilter {
    CPUTargetList,
    ForwardOthersOnly,
    ForwardSelfOnly,
}
