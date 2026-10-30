// Copyright 2023 The arm-gic Authors.
// This project is dual-licensed under Apache 2.0 and MIT terms.
// See LICENSE-APACHE and LICENSE-MIT for details.

//! Driver for the Arm Generic Interrupt Controller version 3 (or 4).

pub mod registers;

use self::registers::{Gicd, GicdCtlr, Gicr, GicrCtlr, Sgi, Waker};
use crate::sysreg::{
    read_icc_iar1_el1, write_icc_ctlr_el1, write_icc_eoir1_el1, write_icc_igrpen0_el1,
    write_icc_igrpen1_el1, write_icc_pmr_el1, write_icc_sgi1r_el1, write_icc_sre_el1,
};
use crate::{IntId, Trigger};
use core::{hint::spin_loop, ptr::NonNull};
use registers::{GicrSgi, GicrTyper, Typer};
use safe_mmio::fields::ReadPureWrite;
use safe_mmio::{field, field_shared, split_fields, UniqueMmioPointer};
use thiserror::Error;

/// An error which may be returned from operations on a GIC Redistributor.
#[derive(Error, Debug, Clone, Copy, Eq, PartialEq)]
pub enum GICRError {
    #[error("Redistributor has already been notified that the connected core is awake")]
    AlreadyAwake,
    #[error("Redistributor has already been notified that the connected core is asleep")]
    AlreadyAsleep,
}

/// Modifies `nth` bit of memory pointed by `registers`.
fn modify_bit(mut registers: UniqueMmioPointer<[ReadPureWrite<u32>]>, nth: usize, set_bit: bool) {
    let reg_num: usize = nth / 32;

    let bit_num: usize = nth % 32;
    let bit_mask: u32 = 1 << bit_num;

    let mut reg_ptr = registers.get(reg_num).unwrap();
    let old_value = reg_ptr.read();

    let new_value: u32 = if set_bit {
        old_value | bit_mask
    } else {
        old_value & !bit_mask
    };

    reg_ptr.write(new_value);
}

/// Sets `nth` bit of memory pointed by `registers`.
fn set_bit(registers: UniqueMmioPointer<[ReadPureWrite<u32>]>, nth: usize) {
    modify_bit(registers, nth, true);
}

/// Clears `nth` bit of memory pointed by `registers`.
fn clear_bit(registers: UniqueMmioPointer<[ReadPureWrite<u32>]>, nth: usize) {
    modify_bit(registers, nth, false);
}

/// Driver for an Arm Generic Interrupt Controller version 3 (or 4).
#[derive(Debug)]
pub struct GicV3<'a> {
    gicd: UniqueMmioPointer<'a, Gicd>,
    gicr_base: *mut GicrSgi,
    /// The number of CPU cores, and hence redistributors.
    cpu_count: usize,
    /// The offset in bytes between the start of redistributor frames.
    gicr_stride: usize,
}

fn get_redistributor_window_size(gicr_base: *mut GicrSgi, gic_v4: bool) -> usize {
    if !gic_v4 {
        return size_of::<GicrSgi>();
    }

    // SAFETY: The caller of `GicV3::new` promised that `gicr_base` was valid
    // and there are no aliases.
    let first_gicr_window = unsafe { UniqueMmioPointer::new(NonNull::new(gicr_base).unwrap()) };

    let first_gicr = field_shared!(first_gicr_window, gicr);

    if field_shared!(first_gicr, typer)
        .read()
        .contains(GicrTyper::VLPIS)
    {
        // In this case GicV4 adds 2 frames:
        // vlpi: 64KiB
        // reserved: 64KiB
        return size_of::<GicrSgi>() * 2;
    }

    size_of::<GicrSgi>()
}

impl GicV3<'_> {
    /// Constructs a new instance of the driver for a GIC with the given distributor and
    /// redistributor base addresses.
    ///
    /// # Safety
    ///
    /// The given base addresses must point to the GIC distributor and redistributor registers
    /// respectively. These regions must be mapped into the address space of the process as device
    /// memory, and not have any other aliases, either via another instance of this driver or
    /// otherwise.
    pub unsafe fn new(
        gicd: *mut Gicd,
        gicr_base: *mut GicrSgi,
        cpu_count: usize,
        gic_v4: bool,
    ) -> Self {
        Self {
            // SAFETY: Our caller promised that `gicd` is a valid and unique pointer to a GIC
            // distributor.
            gicd: unsafe { UniqueMmioPointer::new(NonNull::new(gicd).unwrap()) },
            gicr_base,
            cpu_count,
            gicr_stride: get_redistributor_window_size(gicr_base, gic_v4),
        }
    }

    /// Enables system register access, marks the given CPU core as awake, and sets some basic
    /// configuration.
    ///
    /// `cpu` should be the linear index of the CPU core as used by the GIC redistributor.
    ///
    /// If the core is already marked as awake this will not return any error.
    ///
    /// This disables the use of `ICC_PMR_EL1` as a hint for interrupt distribution, configures a
    /// write to an EOI register to also deactivate the interrupt, and configures preemption groups
    /// for group 0 and group 1 interrupts separately.
    pub fn init_cpu(&mut self, cpu: usize) {
        // Enable system register access.
        write_icc_sre_el1(0x01);

        // Ignore error in case core is already awake.
        let _ = self.redistributor_mark_core_awake(cpu);

        // Disable use of `ICC_PMR_EL1` as a hint for interrupt distribution, configure a write to
        // an EOI register to also deactivate the interrupt, and configure preemption groups for
        // group 0 and group 1 interrupts separately.
        write_icc_ctlr_el1(0);
    }

    /// Initialises the GIC and marks the given CPU core as awake.
    ///
    /// `cpu` should be the linear index of the CPU core as used by the GIC redistributor.
    pub fn setup(&mut self, cpu: usize) {
        self.init_cpu(cpu);

        // Enable affinity routing and non-secure group 1 interrupts.
        field!(self.gicd, ctlr).write(GicdCtlr::ARE_S | GicdCtlr::EnableGrp1NS);

        {
            // Put all SGIs and PPIs into non-secure group 1.
            for cpu in 0..self.cpu_count {
                let mut sgi = self.sgi_ptr(cpu);
                field!(sgi, igroupr0).write(0xffffffff);
            }
        }
        // Put all SPIs into non-secure group 1.
        for i in 1..32 {
            field!(self.gicd, igroupr).get(i).unwrap().write(0xffffffff);
        }

        // Enable group 1 for the current security state.
        Self::enable_group1(true);
    }

    /// Enables or disables group 0 interrupts.
    pub fn enable_group0(enable: bool) {
        write_icc_igrpen0_el1(if enable { 0x01 } else { 0x00 });
    }

    /// Enables or disables group 1 interrupts for the current security state.
    pub fn enable_group1(enable: bool) {
        write_icc_igrpen1_el1(if enable { 0x01 } else { 0x00 });
    }

    /// Enables or disables the interrupt with the given ID.
    ///
    /// If it is an SGI or PPI then the CPU core on which to enable it must also be specified;
    /// otherwise this is ignored and may be `None`.
    pub fn enable_interrupt(&mut self, intid: IntId, cpu: Option<usize>, enable: bool) {
        if intid.is_private() {
            let mut sgi = self.sgi_ptr(cpu.unwrap());
            if enable {
                set_bit(field!(sgi, isenabler0).into(), intid.0 as usize);
            } else {
                set_bit(field!(sgi, icenabler0).into(), intid.0 as usize);
            }
        } else {
            if enable {
                set_bit(field!(self.gicd, isenabler).into(), intid.0 as usize);
            } else {
                set_bit(field!(self.gicd, icenabler).into(), intid.0 as usize);
            }
        };
    }

    /// Enables or disables all interrupts on all CPU cores.
    pub fn enable_all_interrupts(&mut self, enable: bool) {
        for i in 1..32 {
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
        for cpu in 0..self.cpu_count {
            let mut sgi = self.sgi_ptr(cpu);
            if enable {
                field!(sgi, isenabler0).write(0xffffffff);
            } else {
                field!(sgi, icenabler0).write(0xffffffff);
            }
        }
    }

    /// Sets the priority mask for the current CPU core.
    ///
    /// Only interrupts with a higher priority (numerically lower) will be signalled.
    pub fn set_priority_mask(min_priority: u8) {
        write_icc_pmr_el1(min_priority.into());
    }

    /// Sets the priority of the interrupt with the given ID.
    ///
    /// Note that lower numbers correspond to higher priorities; i.e. 0 is the highest priority, and
    /// 255 is the lowest.
    pub fn set_interrupt_priority(&mut self, intid: IntId, cpu: Option<usize>, priority: u8) {
        // Affinity routing is enabled, so use the GICR for SGIs and PPIs.
        if intid.is_private() {
            let mut sgi = self.sgi_ptr(cpu.unwrap());
            field!(sgi, ipriorityr)
                .get(intid.0 as usize)
                .unwrap()
                .write(priority);
        } else {
            field!(self.gicd, ipriorityr)
                .get(intid.0 as usize)
                .unwrap()
                .write(priority);
        }
    }

    /// Configures the trigger type for the interrupt with the given ID.
    pub fn set_trigger(&mut self, intid: IntId, cpu: Option<usize>, trigger: Trigger) {
        let index = (intid.0 / 16) as usize;
        let bit = 1 << (((intid.0 % 16) * 2) + 1);

        // Affinity routing is enabled, so use the GICR for SGIs and PPIs.
        if intid.is_private() {
            let mut sgi = self.sgi_ptr(cpu.unwrap());
            let mut icfgr = field!(sgi, icfgr);
            let mut register = icfgr.get(index).unwrap();
            let v = register.read();
            register.write(match trigger {
                Trigger::Edge => v | bit,
                Trigger::Level => v & !bit,
            });
        } else {
            let mut icfgr = field!(self.gicd, icfgr);
            let mut register = icfgr.get(index).unwrap();
            let v = register.read();
            register.write(match trigger {
                Trigger::Edge => v | bit,
                Trigger::Level => v & !bit,
            });
        };
    }

    /// Assigns the interrupt with id `intid` to interrupt group `group`.
    pub fn set_group(&mut self, intid: IntId, cpu: Option<usize>, group: Group) {
        if intid.is_private() {
            let mut sgi = self.sgi_ptr(cpu.unwrap());
            if let Group::Secure(sg) = group {
                clear_bit(field!(sgi, igroupr0).into(), intid.0 as usize);
                let igrpmodr = field!(sgi, igrpmodr0).into();
                match sg {
                    SecureIntGroup::Group1S => set_bit(igrpmodr, intid.0 as usize),
                    SecureIntGroup::Group0 => clear_bit(igrpmodr, intid.0 as usize),
                }
            } else {
                set_bit(field!(sgi, igroupr0).into(), intid.0 as usize);
                clear_bit(field!(sgi, igrpmodr0).into(), intid.0 as usize);
            }
        } else {
            if let Group::Secure(sg) = group {
                let igroupr = field!(self.gicd, igroupr);
                clear_bit(igroupr.into(), intid.0 as usize);
                let igrpmodr = field!(self.gicd, igrpmodr);
                match sg {
                    SecureIntGroup::Group1S => set_bit(igrpmodr.into(), intid.0 as usize),
                    SecureIntGroup::Group0 => clear_bit(igrpmodr.into(), intid.0 as usize),
                }
            } else {
                set_bit(field!(self.gicd, igroupr).into(), intid.0 as usize);
                clear_bit(field!(self.gicd, igrpmodr).into(), intid.0 as usize);
            }
        };
    }

    /// Sends a software-generated interrupt (SGI) to the given cores.
    pub fn send_sgi(intid: IntId, target: SgiTarget) {
        assert!(intid.is_sgi());

        let sgi_value = match target {
            SgiTarget::All => {
                let irm = 0b1;
                (u64::from(intid.0 & 0x0f) << 24) | (irm << 40)
            }
            SgiTarget::List {
                affinity3,
                affinity2,
                affinity1,
                target_list,
            } => {
                let irm = 0b0;
                u64::from(target_list)
                    | (u64::from(affinity1) << 16)
                    | (u64::from(intid.0 & 0x0f) << 24)
                    | (u64::from(affinity2) << 32)
                    | (irm << 40)
                    | (u64::from(affinity3) << 48)
            }
        };

        write_icc_sgi1r_el1(sgi_value);
    }

    /// Gets the ID of the highest priority signalled interrupt, and acknowledges it.
    ///
    /// Returns `None` if there is no pending interrupt of sufficient priority.
    pub fn get_and_acknowledge_interrupt() -> Option<IntId> {
        let intid = IntId(read_icc_iar1_el1());
        if intid == IntId::SPECIAL_NONE {
            None
        } else {
            Some(intid)
        }
    }

    /// Informs the interrupt controller that the CPU has completed processing the given interrupt.
    /// This drops the interrupt priority and deactivates the interrupt.
    pub fn end_interrupt(intid: IntId) {
        write_icc_eoir1_el1(intid.0)
    }

    /// Returns information about what the GIC implementation supports.
    pub fn typer(&self) -> Typer {
        field_shared!(self.gicd, typer).read()
    }

    /// Returns a pointer to the GIC distributor registers.
    ///
    /// This may be used to read and write the registers directly for functionality not yet
    /// supported by this driver.
    pub fn gicd_ptr(&mut self) -> UniqueMmioPointer<Gicd> {
        self.gicd.reborrow()
    }

    /// Returns a pointer to the GIC redistributor, SGI and PPI registers.
    fn gicr_sgi_ptr(&mut self, cpu: usize) -> UniqueMmioPointer<GicrSgi> {
        assert!(cpu < self.cpu_count);
        // SAFETY: The caller of `GicV3::new` promised that `gicr_base` and `gicr_stride` were valid
        // and there are no aliases.
        unsafe {
            UniqueMmioPointer::new(
                NonNull::new(self.gicr_base.wrapping_byte_add(cpu * self.gicr_stride)).unwrap(),
            )
        }
    }

    /// Returns a pointer to the GIC redistributor registers.
    ///
    /// This may be used to read and write the registers directly for functionality not yet
    /// supported by this driver.
    pub fn gicr_ptr(&mut self, cpu: usize) -> UniqueMmioPointer<Gicr> {
        // SAFETY: We only split out a single field.
        unsafe { split_fields!(self.gicr_sgi_ptr(cpu), gicr) }
    }

    /// Returns a pointer to the GIC redistributor SGI and PPI registers.
    ///
    /// This may be used to read and write the registers directly for functionality not yet
    /// supported by this driver.
    pub fn sgi_ptr(&mut self, cpu: usize) -> UniqueMmioPointer<Sgi> {
        // SAFETY: We only split out a single field.
        unsafe { split_fields!(self.gicr_sgi_ptr(cpu), sgi) }
    }

    /// Blocks until register write for the current Security state is no longer in progress.
    pub fn gicd_barrier(&self) {
        while field_shared!(self.gicd, ctlr)
            .read()
            .contains(GicdCtlr::RWP)
        {}
    }

    fn gicd_modify_control(&mut self, f: impl FnOnce(GicdCtlr) -> GicdCtlr) {
        let gicd_ctlr = field_shared!(self.gicd, ctlr).read();

        field!(self.gicd, ctlr).write(f(gicd_ctlr));

        self.gicd_barrier();
    }

    /// Clears specified bits in GIC distributor control register.
    pub fn gicd_clear_control(&mut self, flags: GicdCtlr) {
        self.gicd_modify_control(|old| old - flags);
    }

    /// Sets specified bits in GIC distributor control register.
    pub fn gicd_set_control(&mut self, flags: GicdCtlr) {
        self.gicd_modify_control(|old| old | flags);
    }

    /// Blocks until register write for the current Security state is no longer in progress.
    pub fn gicr_barrier(&mut self, cpu: usize) {
        let gicr = self.gicr_ptr(cpu);
        while field_shared!(gicr, ctlr).read().contains(GicrCtlr::RWP) {}
    }

    /// Informs the GIC redistributor that the core has awakened.
    ///
    /// Blocks until `GICR_WAKER.ChildrenAsleep` is cleared.
    pub fn redistributor_mark_core_awake(&mut self, cpu: usize) -> Result<(), GICRError> {
        let mut gicr = self.gicr_ptr(cpu);
        let mut waker = field!(gicr, waker);
        let mut gicr_waker = waker.read();

        // The WAKER_PS_BIT should be changed to 0 only when WAKER_CA_BIT is 1.
        if !gicr_waker.contains(Waker::CHILDREN_ASLEEP) {
            return Err(GICRError::AlreadyAwake);
        }

        // Mark the connected core as awake.
        gicr_waker -= Waker::PROCESSOR_SLEEP;
        waker.write(gicr_waker);

        // Wait till the WAKER_CA_BIT changes to 0.
        while waker.read().contains(Waker::CHILDREN_ASLEEP) {
            spin_loop();
        }

        Ok(())
    }

    /// Informs the GIC redistributor that the core is asleep.
    ///
    /// Blocks until `GICR_WAKER.ChildrenAsleep` is set.
    pub fn redistributor_mark_core_asleep(&mut self, cpu: usize) -> Result<(), GICRError> {
        let mut gicr = self.gicr_ptr(cpu);
        let mut waker = field!(gicr, waker);
        let mut gicr_waker = waker.read();

        // The WAKER_PS_BIT should be changed to 1 only when WAKER_CA_BIT is 0.
        if gicr_waker.contains(Waker::CHILDREN_ASLEEP) {
            return Err(GICRError::AlreadyAsleep);
        }

        // Mark the connected core as asleep.
        gicr_waker |= Waker::PROCESSOR_SLEEP;
        waker.write(gicr_waker);

        // Wait till the WAKER_CA_BIT changes to 1.
        while !waker.read().contains(Waker::CHILDREN_ASLEEP) {
            spin_loop();
        }

        Ok(())
    }
}

// SAFETY: The GIC interface can be accessed from any CPU core.
unsafe impl Send for GicV3<'_> {}

// SAFETY: Any operations which change state require `&mut GicV3`, so `&GicV3` is fine to share.
unsafe impl Sync for GicV3<'_> {}

/// The group configuration for an interrupt.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Group {
    Secure(SecureIntGroup),
    Group1NS,
}

/// The group configuration for an interrupt.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum SecureIntGroup {
    /// The interrupt belongs to Secure Group 1.
    Group1S,
    /// The interrupt belongs to Group 0.
    Group0,
}

/// The target specification for a software-generated interrupt.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum SgiTarget {
    /// The SGI is routed to all CPU cores except the current one.
    All,
    /// The SGI is routed to the CPU cores matching the given affinities and list.
    List {
        affinity3: u8,
        affinity2: u8,
        affinity1: u8,
        target_list: u16,
    },
}
