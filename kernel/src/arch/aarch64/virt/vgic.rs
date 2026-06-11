// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use super::VCPU_MANAGER;
use crate::sync::SpinLock;
use core::arch::asm;
use spin::Once;

const MAX_LR: usize = 4;
const MAX_PENDING: usize = 64;
const MAX_VCPUS: usize = 4;
pub const MAX_IRQS_WORDS: usize = 32;

// Qemu default base address
const VGICD_BASE: u64 = 0x0800_0000;
const VGICD_SIZE: u64 = 0x0001_0000;
const VGICR_BASE: u64 = 0x080A_0000;
const VGICR_SIZE: u64 = 0x00F6_0000;
const GICR_VCPU_SIZE: u64 = 0x20000;

#[derive(Debug, Copy, Clone)]
pub struct VgicDistributor {
    pub ctlr: u32,
    pub isenabler: [u32; MAX_IRQS_WORDS],
    pub ispendr: [u32; MAX_IRQS_WORDS],
    pub isactiver: [u32; MAX_IRQS_WORDS],
    pub ipriorityr: [u32; MAX_IRQS_WORDS * 8],
}

#[derive(Debug, Copy, Clone)]
pub struct VgicRedistributor {
    pub isenabler0: u32,
    pub ispendr0: u32,
    pub isactiver0: u32,
    pub ipriorityr0: [u32; 8],

    // Virq injection queue.
    pub pending_irqs: [u32; MAX_PENDING],
    pub pending_head: usize,
    pub pending_tail: usize,
    pub pending_count: usize,
    // Recording how many lrs are used like KVM doing.
    pub used_lrs: usize,
    pub lr_intids: [u32; MAX_LR],
}

impl VgicDistributor {
    pub const fn new() -> Self {
        Self {
            ctlr: 0,
            isenabler: [0; MAX_IRQS_WORDS],
            ispendr: [0; MAX_IRQS_WORDS],
            isactiver: [0; MAX_IRQS_WORDS],
            ipriorityr: [0; MAX_IRQS_WORDS * 8],
        }
    }
}

impl VgicRedistributor {
    pub const fn new() -> Self {
        Self {
            isenabler0: 0,
            ispendr0: 0,
            isactiver0: 0,
            ipriorityr0: [0; 8],
            pending_irqs: [0; MAX_PENDING],
            pending_head: 0,
            pending_tail: 0,
            pending_count: 0,
            used_lrs: 0,
            lr_intids: [0; MAX_LR],
        }
    }

    pub fn push_queue(&mut self, intid: u32) {
        if self.pending_count >= MAX_PENDING {
            return;
        }

        // In case of existing same Intid.
        let mut curr = self.pending_head;
        for _ in 0..self.pending_count {
            if self.pending_irqs[curr] == intid {
                return;
            }
            curr = (curr + 1) % MAX_PENDING;
        }

        self.pending_irqs[self.pending_tail] = intid;
        self.pending_tail = (self.pending_tail + 1) % MAX_PENDING;
        self.pending_count += 1;
    }
}

pub struct Vgic {
    pub dist: SpinLock<VgicDistributor>,
    pub redists: [SpinLock<VgicRedistributor>; MAX_VCPUS],
}

impl Vgic {
    pub fn new() -> Self {
        Self {
            dist: SpinLock::new(VgicDistributor::new()),
            redists: [
                SpinLock::new(VgicRedistributor::new()),
                SpinLock::new(VgicRedistributor::new()),
                SpinLock::new(VgicRedistributor::new()),
                SpinLock::new(VgicRedistributor::new()),
            ],
        }
    }
}

pub static VGIC: Once<Vgic> = Once::new();
pub fn init() {
    VGIC.call_once(Vgic::new);
}
// Set mmio to access distributor and redistributor.
struct MmioAccess {
    addr: u64,
    is_write: bool,
    size: usize,
    reg_index: usize,
}

#[inline]
pub fn get_vgic() -> &'static Vgic {
    #[cfg(test)]
    VGIC.call_once(Vgic::new);

    VGIC.get().expect("[vGIC] Error: VGIC is not initialized!")
}

impl MmioAccess {
    fn parse(esr: u64, far: u64) -> Option<Self> {
        if (esr & (1 << 24)) == 0 {
            return None;
        }

        Some(Self {
            addr: far,
            is_write: (esr & (1 << 6)) != 0,
            size: 1 << ((esr >> 22) & 0b11),
            reg_index: ((esr >> 16) & 0b11111) as usize,
        })
    }
}

pub fn handle_data_abort(vcpu_id: usize, esr: u64, far: u64, regs: &mut [u64; 31]) -> bool {
    let access = match MmioAccess::parse(esr, far) {
        Some(acc) => acc,
        None => return false,
    };

    if access.addr >= VGICD_BASE && access.addr < VGICD_BASE + VGICD_SIZE {
        let offset = access.addr - VGICD_BASE;
        emulate_access(vcpu_id, &access, offset, regs, true);
        true
    } else if access.addr >= VGICR_BASE && access.addr < VGICR_BASE + VGICR_SIZE {
        let relative_addr = access.addr - VGICR_BASE;
        let target_vcpu_id = (relative_addr / GICR_VCPU_SIZE) as usize;
        let offset = relative_addr % GICR_VCPU_SIZE;
        emulate_access(target_vcpu_id, &access, offset, regs, false);
        true
    } else {
        false
    }
}

fn emulate_access(
    target_vcpu: usize,
    access: &MmioAccess,
    offset: u64,
    regs: &mut [u64; 31],
    is_dist: bool,
) {
    let is_zero_reg = access.reg_index == 31;

    if access.is_write {
        let val = if is_zero_reg {
            0
        } else {
            (regs[access.reg_index] & 0xFFFFFFFF) as u32
        };

        if is_dist {
            handle_gicd_write(offset, val);
        } else {
            handle_gicr_write(target_vcpu, offset, val);
        }
    } else {
        let val = if is_dist {
            handle_gicd_read(offset)
        } else {
            handle_gicr_read(target_vcpu, offset)
        };

        if !is_zero_reg {
            regs[access.reg_index] = val as u64;
        }
    }
}

fn handle_gicd_write(offset: u64, val: u32) {
    let mut pending_intids = [0u32; 32];
    let mut pending_count = 0;
    // Set a scope, so that we can release lock automatically.
    {
        let mut dist = get_vgic().dist.lock();
        match offset {
            0x0000 => dist.ctlr = val,
            0x0100..=0x017C => {
                let index = ((offset - 0x0100) / 4) as usize;
                let newly_enabled = val & !dist.isenabler[index];
                dist.isenabler[index] |= val;
                let pending_to_push = dist.ispendr[index] & newly_enabled;
                if pending_to_push != 0 {
                    for i in 0..32 {
                        if (pending_to_push & (1 << i)) != 0 {
                            pending_intids[pending_count] = (index * 32 + i) as u32;
                            pending_count += 1;
                        }
                    }
                }
            }
            0x0180..=0x01FC => dist.isenabler[((offset - 0x0180) / 4) as usize] &= !val,
            0x0400..=0x07F8 => dist.ipriorityr[((offset - 0x0400) / 4) as usize] = val,
            _ => {}
        }
    }

    if pending_count > 0 {
        // To Do: When GICv3 is improved in the future, GICD_IROUTER<n> should be read here to determine the target vCPU.
        let mut redist = get_vgic().redists[0].lock();
        for &intid in &pending_intids[..pending_count] {
            redist.push_queue(intid);
        }
    }
}

fn handle_gicr_write(vcpu_id: usize, offset: u64, val: u32) {
    if vcpu_id >= MAX_VCPUS {
        return;
    }
    let mut redist = get_vgic().redists[vcpu_id].lock();
    match offset {
        // 0x10100 => redist.isenabler0 |= val,
        0x10100 => {
            let newly_enabled = val & !redist.isenabler0;
            redist.isenabler0 |= val;
            let pending_to_push = redist.ispendr0 & newly_enabled;
            if pending_to_push != 0 {
                for i in 0..32 {
                    if (pending_to_push & (1 << i)) != 0 {
                        redist.push_queue(i);
                    }
                }
            }
            // When Guest enables IRQ 27 (virtual timer), clear CNTV_CTL_EL0.IMASK
            // that was set by hyper_trap_irq when the timer fired before Guest
            // enabled isenabler0. Without this, the physical timer stays permanently
            // silent — no timer ticks → Guest scheduler can't wake processes.
            if (newly_enabled & (1 << 27)) != 0 {
                unsafe {
                    let mut ctl: u64;
                    asm!("mrs {}, CNTV_CTL_EL0", out(reg) ctl);
                    ctl &= !(1u64 << 1);
                    asm!("msr CNTV_CTL_EL0, {}", in(reg) ctl);
                    asm!("isb", options(nostack));
                }
            }
        }
        0x10180 => redist.isenabler0 &= !val,
        0x10200 => redist.ispendr0 |= val,
        0x10280 => redist.ispendr0 &= !val,
        0x10300 => redist.isactiver0 |= val,
        0x10380 => redist.isactiver0 &= !val,
        0x10400..=0x1041C => redist.ipriorityr0[((offset - 0x10400) / 4) as usize] = val,
        _ => {}
    }
}

fn handle_gicd_read(offset: u64) -> u32 {
    let dist = get_vgic().dist.lock();
    match offset {
        0x0000 => dist.ctlr,
        0x0004 => 0x00000006,
        // 0x43B represent Arm Ltd.
        0x0008 => 0x43B00000,
        0x0100..=0x017C => dist.isenabler[((offset - 0x0100) / 4) as usize],
        0x0180..=0x01FC => dist.isenabler[((offset - 0x0180) / 4) as usize],
        0x0400..=0x07F8 => dist.ipriorityr[(((offset - 0x0400) / 4) as usize)],
        0xFFE8 => 0x00000030,
        _ => 0,
    }
}

fn handle_gicr_read(vcpu_id: usize, offset: u64) -> u32 {
    if vcpu_id >= MAX_VCPUS {
        return 0;
    }
    let redist = get_vgic().redists[vcpu_id].lock();
    match offset {
        0x0008 => {
            let mut val = (vcpu_id as u32) << 8;
            let active_vcpus = unsafe { VCPU_MANAGER.0.vcpu_count() };
            if vcpu_id == active_vcpus - 1 {
                val |= 1 << 4;
            }
            val
        }
        0x000C => {
            //Nowaday, we only have one core and basic mapping, so the high 32 bits are 0.
            0
        }
        0xFFE8 => 0x00000030,
        0x10100 => redist.isenabler0,
        0x10180 => redist.isenabler0,
        0x10200 => redist.ispendr0,
        0x10300 => redist.isactiver0,
        0x10400..=0x1041C => redist.ipriorityr0[((offset - 0x10400) / 4) as usize],
        _ => 0,
    }
}

// Per-CPU Initialization (called by vCPU on first run)
// To Do: Distribut every vcpu a Redistributor.
pub fn cpu_init(vcpu_id: usize) {
    unsafe {
        // 1. Enable System Register access for EL2 (ICC_SRE_EL2)
        let mut sre: u64;
        asm!("mrs {}, ICC_SRE_EL2", out(reg) sre);
        if (sre & 0x9) != 0x9 {
            sre |= 0x9;
            asm!("msr ICC_SRE_EL2, {}", in(reg) sre);
            asm!("isb");
        }

        // 2. Enable vGIC
        let hcr: u64 = 1;
        asm!("msr ICH_HCR_EL2, {}", in(reg) hcr);

        // 3. Configure VMCR (Group 0/1 Enable)
        let vmcr: u64 = 0x3;
        asm!("msr ICH_VMCR_EL2, {}", in(reg) vmcr);

        // Clear all LRs
        for i in 0..MAX_LR {
            write_lr(i, 0);
        }
    }
}

/// Clear all ICH_LR registers to invalidate pending/active virtual interrupts.
/// Called during guest shutdown to ensure no stale vGIC state leaks to the host.
pub unsafe fn clear_all_lrs() {
    for i in 0..MAX_LR {
        write_lr(i, 0);
    }
}

pub fn inject(vcpu_id: usize, intid: u32) {
    unsafe {
        if vcpu_id >= MAX_VCPUS || intid >= 1024 {
            return;
        }
        let mut is_enabled;
        if intid < 32 {
            let mut redist = get_vgic().redists[vcpu_id].lock();
            redist.ispendr0 |= 1 << intid;
            if (redist.isenabler0 & (1 << intid)) != 0 {
                redist.push_queue(intid);
            }
        } else {
            // SPI
            let mut dist = get_vgic().dist.lock();
            let index = (intid / 32) as usize;
            let mask = 1 << (intid % 32);
            dist.ispendr[index] |= mask;
            is_enabled = (dist.isenabler[index] & mask) != 0;
            drop(dist);

            if is_enabled {
                let mut redist = get_vgic().redists[vcpu_id].lock();
                redist.push_queue(intid);
            }
        }
    }
}

// ICH_LR<n>_EL2 - List Register, used to inject virtual interrupts to guest
//
// Bit layout:
// [63:62] State       - Virtual interrupt state
//                       00 = Invalid (slot unused)
//                       01 = Pending
//                       10 = Active
//                       11 = Pending and Active
// [61]    HW          - Hardware interrupt
//                       0 = Virtual interrupt (software-generated)
//                       1 = Physical interrupt (maps to a physical IRQ, requires pINTID)
// [60]    Group       - Interrupt group
//                       0 = Group 0 (FIQ)
//                       1 = Group 1 (IRQ)
// [59]    Reserved
// [55:48] Priority    - Virtual interrupt priority (8-bit, lower = higher priority)
//                       e.g. 0xA0 = lower priority
// [47:45] Reserved
// [44:32] pINTID      - Physical INTID (only valid when HW=1)
//                       Maps virtual interrupt to a physical interrupt for EOI deactivation
// [31:0]  vINTID      - Virtual INTID to be injected into the guest (bits [23:0] effective)
pub fn flush(vcpu_id: usize) {
    if vcpu_id >= MAX_VCPUS {
        return;
    }

    let mut dist = get_vgic().dist.lock();
    let mut redist = get_vgic().redists[vcpu_id].lock();

    unsafe {
        let mut current_lr = 0;

        // Phase 1: All PPI Active interrupts (Active-only and Active+Pending).
        let mut active_word = redist.isactiver0;
        while active_word != 0 && current_lr < MAX_LR {
            let bit = active_word.trailing_zeros();
            let intid = bit as u32;
            active_word &= !(1 << bit);

            let is_pending = (redist.ispendr0 & (1 << intid)) != 0;
            let is_enabled = (redist.isenabler0 & (1 << intid)) != 0;
            let mut state_bits: u64 = 0b10;
            if is_pending && is_enabled {
                state_bits |= 0b01;
                redist.ispendr0 &= !(1 << intid);
            }

            let is_hw = intid == 27;
            let hw_bit = if is_hw { 1u64 << 61 } else { 0 };
            let pintid_bits = if is_hw { (intid as u64) << 32 } else { 0 };

            let lr_val: u64 = (state_bits << 62)
                | hw_bit
                | (1 << 60)
                | (0xA0 << 48)
                | pintid_bits
                | (intid as u64);
            write_lr(current_lr, lr_val);
            redist.lr_intids[current_lr] = intid;
            current_lr += 1;
        }

        // Phase 2: Pending interrupts from queue (state 01) — including timer IRQ 27.
        // Elevated above SPI Active to ensure timer delivery before LR overflow.
        let mut processed_count = 0;
        let original_count = redist.pending_count;

        while processed_count < original_count && current_lr < MAX_LR {
            let intid = redist.pending_irqs[redist.pending_head];
            redist.pending_head = (redist.pending_head + 1) % MAX_PENDING;
            redist.pending_count -= 1;
            processed_count += 1;
            if is_irq_active_locked(&redist, &dist, intid) {
                continue;
            }

            let is_pending = is_irq_pending_locked(&redist, &dist, intid);
            let is_enabled = is_irq_enabled_locked(&redist, &dist, intid);

            if is_pending && is_enabled {
                let state_bits: u64 = 0b01;
                clear_irq_pending_locked(&mut redist, &mut dist, intid);

                let is_hw = intid == 27;
                let hw_bit = if is_hw { 1u64 << 61 } else { 0 };
                let pintid_bits = if is_hw { (intid as u64) << 32 } else { 0 };

                let lr_val: u64 = (state_bits << 62)
                    | hw_bit
                    | (1 << 60)
                    | (0xA0 << 48)
                    | pintid_bits
                    | (intid as u64);
                write_lr(current_lr, lr_val);
                redist.lr_intids[current_lr] = intid;
                current_lr += 1;
            }
        }

        // Phase 3: SPI Active interrupts (lowest priority for LR allocation).
        for i in 1..MAX_IRQS_WORDS {
            if current_lr >= MAX_LR {
                break;
            }
            let mut spi_active_word = dist.isactiver[i];

            while spi_active_word != 0 && current_lr < MAX_LR {
                let bit = spi_active_word.trailing_zeros();
                let intid = (i * 32) as u32 + bit as u32;
                spi_active_word &= !(1 << bit);
                let is_pending = is_irq_pending_locked(&redist, &dist, intid);
                let is_enabled = is_irq_enabled_locked(&redist, &dist, intid);
                let mut state_bits: u64 = 0b10;

                if is_pending && is_enabled {
                    state_bits |= 0b01;
                    dist.ispendr[i] &= !(1 << bit);
                }

                let lr_val: u64 = (state_bits << 62) | (1 << 60) | (0xA0 << 48) | (intid as u64);
                write_lr(current_lr, lr_val);
                redist.lr_intids[current_lr] = intid;
                current_lr += 1;
            }
        }

        redist.used_lrs = current_lr;
    }
}

pub fn sync(vcpu_id: usize) {
    if vcpu_id >= MAX_VCPUS {
        return;
    }

    let mut dist = get_vgic().dist.lock();
    let mut redist = get_vgic().redists[vcpu_id].lock();

    unsafe {
        for i in 0..redist.used_lrs {
            let lr_val = read_lr(i);
            let state = (lr_val >> 62) & 0b11;
            let intid = redist.lr_intids[i];
            let hw = (lr_val >> 61) & 1;

            // HW-mapped LR with state != Invalid: the physical interrupt is
            // Active (Guest hasn't done virtual EOI yet).  Invalidating the
            // LR without DIR destroys the HW mapping, so the Guest's future
            // virtual EOI won't auto-deactivate the physical INTID, leaving
            // it permanently Active and silencing future assertions.
            // DIR on an Active interrupt transitions it to Inactive;
            // on Active-and-Pending it transitions to Pending (re-triggers).
            // DIR on an Inactive interrupt is a safe no-op per GICv3 spec.
            if hw != 0 && state != 0 {
                let p_intid = (lr_val & 0x3FF) as u64;
                core::arch::asm!("msr ICC_DIR_EL1, {}", in(reg) p_intid, options(nostack));
                core::arch::asm!("isb", options(nostack));
            }

            if state == 0 {
                clear_irq_state_locked(&mut redist, &mut dist, intid);
            } else {
                sync_irq_state_locked(&mut redist, &mut dist, intid, state);
                if (state & 0b01) != 0 {
                    redist.push_queue(intid);
                }
            }

            write_lr(i, 0);
        }

        redist.used_lrs = 0;
    }
}

pub fn inject_irq(vcpu_id: usize, intid: u32) {
    if vcpu_id >= MAX_VCPUS {
        return;
    }
    unsafe {
        inject(vcpu_id, intid);
    }
}

pub fn inject_fiq(_intid: u32) {
    // ...
}

#[cfg(test)]
pub static mut MOCK_LR: [u64; MAX_LR] = [0; MAX_LR];

unsafe fn read_lr(index: usize) -> u64 {
    #[cfg(test)]
    {
        if index < MAX_LR {
            MOCK_LR[index]
        } else {
            0
        }
    }

    #[cfg(not(test))]
    {
        let val: u64;
        match index {
            0 => asm!("mrs {}, ICH_LR0_EL2", out(reg) val),
            1 => asm!("mrs {}, ICH_LR1_EL2", out(reg) val),
            2 => asm!("mrs {}, ICH_LR2_EL2", out(reg) val),
            3 => asm!("mrs {}, ICH_LR3_EL2", out(reg) val),
            _ => val = 0,
        }
        val
    }
}

unsafe fn write_lr(index: usize, val: u64) {
    #[cfg(test)]
    {
        if index < MAX_LR {
            MOCK_LR[index] = val;
        }
    }
    #[cfg(not(test))]
    {
        match index {
            0 => asm!("msr ICH_LR0_EL2, {}", in(reg) val),
            1 => asm!("msr ICH_LR1_EL2, {}", in(reg) val),
            2 => asm!("msr ICH_LR2_EL2, {}", in(reg) val),
            3 => asm!("msr ICH_LR3_EL2, {}", in(reg) val),
            _ => (),
        }
    }
}

fn clear_irq_state_locked(redist: &mut VgicRedistributor, dist: &mut VgicDistributor, intid: u32) {
    if intid < 32 {
        redist.isactiver0 &= !(1 << intid);
    } else {
        // SPI should have lock.
        let index = (intid / 32) as usize;
        let mask = 1 << (intid % 32);
        dist.isactiver[index] &= !mask;
    }
}

fn sync_irq_state_locked(
    redist: &mut VgicRedistributor,
    dist: &mut VgicDistributor,
    intid: u32,
    state: u64,
) {
    let is_pending = (state & 0b01) != 0;
    let is_active = (state & 0b10) != 0;

    if intid < 32 {
        if is_pending {
            redist.ispendr0 |= 1 << intid;
        }

        if is_active {
            redist.isactiver0 |= 1 << intid;
        } else {
            redist.isactiver0 &= !(1 << intid);
        }
    } else {
        let index = (intid / 32) as usize;
        let mask = 1 << (intid % 32);
        if is_pending {
            dist.ispendr[index] |= mask;
        }

        if is_active {
            dist.isactiver[index] |= mask;
        } else {
            dist.isactiver[index] &= !mask;
        }
    }
}

fn is_irq_active_locked(redist: &VgicRedistributor, dist: &VgicDistributor, intid: u32) -> bool {
    if intid < 32 {
        (redist.isactiver0 & (1 << intid)) != 0
    } else {
        (dist.isactiver[(intid / 32) as usize] & (1 << (intid % 32))) != 0
    }
}

fn is_irq_pending_locked(redist: &VgicRedistributor, dist: &VgicDistributor, intid: u32) -> bool {
    if intid < 32 {
        (redist.ispendr0 & (1 << intid)) != 0
    } else {
        (dist.ispendr[(intid / 32) as usize] & (1 << (intid % 32))) != 0
    }
}

fn is_irq_enabled_locked(redist: &VgicRedistributor, dist: &VgicDistributor, intid: u32) -> bool {
    if intid < 32 {
        (redist.isenabler0 & (1 << intid)) != 0
    } else {
        (dist.isenabler[(intid / 32) as usize] & (1 << (intid % 32))) != 0
    }
}

fn clear_irq_pending_locked(
    redist: &mut VgicRedistributor,
    dist: &mut VgicDistributor,
    intid: u32,
) {
    if intid < 32 {
        redist.ispendr0 &= !(1 << intid);
    } else {
        let index = (intid / 32) as usize;
        let mask = 1 << (intid % 32);
        dist.ispendr[index] &= !mask;
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    fn setup_test_env() {
        unsafe {
            super::MOCK_LR.fill(0);
        }
    }

    #[test]
    fn test_vgic_queue_deduplication() {
        setup_test_env();
        let mut redist = VgicRedistributor::new();

        // Verify normal queuing.
        redist.push_queue(27);
        redist.push_queue(30);
        assert_eq!(redist.pending_count, 2);
        assert_eq!(redist.pending_irqs[0], 27);
        assert_eq!(redist.pending_irqs[1], 30);

        // Verify deadlock prevention optimization: ghost reuse deduplication.
        redist.push_queue(27);
        assert_eq!(
            redist.pending_count, 2,
            "Duplicate interrupt should be ignored!"
        );
    }

    #[test]
    fn test_vgic_flush_and_sync_lifecycle() {
        setup_test_env();
        init();
        let vcpu_id = 0;

        // Simulating enabling 27 interrupt
        {
            let mut redist = get_vgic().redists[vcpu_id].lock();
            redist.isenabler0 |= 1 << 27;
        }

        inject(vcpu_id, 27);
        {
            let redist = get_vgic().redists[vcpu_id].lock();
            assert_eq!(redist.pending_count, 1);
        }

        flush(vcpu_id);

        unsafe {
            let lr_val = super::MOCK_LR[0];
            let state = (lr_val >> 62) & 0b11;
            let intid = (lr_val & 0xFFFFFFFF) as u32;
            assert_eq!(state, 0b01, "Interrupt should be Pending in LR");
            assert_eq!(intid, 27, "IntID in LR should be 27");
        }

        {
            let redist = get_vgic().redists[vcpu_id].lock();
            assert_eq!(redist.pending_count, 0, "Queue should be empty after flush");
            assert_eq!(redist.used_lrs, 1, "Should record 1 used LR");
        }

        // Simulating hardware EOI.
        unsafe {
            super::MOCK_LR[0] = 0;
        }
        sync(vcpu_id);

        {
            let redist = get_vgic().redists[vcpu_id].lock();
            assert_eq!(redist.used_lrs, 0, "Used LRs should be reset");
            assert_eq!(
                (redist.isactiver0 & (1 << 27)),
                0,
                "Active state should be cleared"
            );
        }
    }
}
