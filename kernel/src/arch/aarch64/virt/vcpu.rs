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

use core::arch::asm;
use super::{
    hyper::{read_hcr_el2, write_hcr_el2}, vgic
};

/// HCR_EL2_VI: Enable virtual IRQ.
const HCR_EL2_VI: u64 = 1 << 7;
/// HCR_EL2_VF: Enable virtual FIQ.
const HCR_EL2_VF: u64 = 1 << 6;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum VcpuState {
    Stopped,
    Running,
    Paused,
    Exited,
}

/// Using #[repr(C)] to ensure compatibility with ARM AAPCS64 calling convention,
/// using #[repr(align(16))] to ensure 16-byte alignment, satisfying SIMD register alignment requirements
#[derive(Debug, Default)]
#[repr(C)]
#[repr(align(16))]
pub struct VcpuStateStruct {
    pub regs: [u64; 31],
    pub elr_el2: u64,
    pub sp: u64,
    pub pstate: u64,
    pub spsr: u64,
    pub vbar_el1: u64,
    pub sctlr_el1:  u64,
    pub ttbr0_el1:  u64,  
    pub ttbr1_el1:  u64, 
    pub tcr_el1:    u64,
    pub mair_el1:   u64,
    pub elr_el1:    u64,
    pub spsr_el1:   u64,
    pub sp_el0:     u64,
    pub tpidr_el0:  u64,
    pub tpidr_el1:  u64,
    pub esr_el1:    u64,
    pub far_el1:    u64,
}

impl VcpuStateStruct {
    #[inline]
    pub fn new() -> Self {
        Self::default()
    }
    
    #[inline]
    pub fn is_valid(&self) -> bool {
        self.elr_el2 != 0 && self.sp != 0
    }
    
    #[inline]
    pub fn reset(&mut self) {
        self.regs = [0; 31];
        self.elr_el2 = 0;
        self.sp = 0;
        self.pstate = 0;
        self.spsr = 0;
        self.vbar_el1 = 0;
    }
    
    #[inline]
    pub fn elr(&self) -> u64 {
        self.elr_el2
    }
    
    #[inline]
    pub fn set_elr(&mut self, elr: u64) {
        self.elr_el2 = elr;
    }
    
    #[inline]
    pub fn spsr(&self) -> u64 {
        self.spsr
    }
    
    #[inline]
    pub fn set_spsr(&mut self, spsr: u64) {
        self.spsr = spsr;
    }
}

#[repr(align(16))]
pub struct Vcpu {
    id: usize,
    state: VcpuState,
    context: VcpuStateStruct,
    entry: usize,
    stack_top: usize,
    pending_irq: bool,
    pending_fiq: bool,
}

impl Vcpu {
    #[inline]
    pub fn new(id: usize, entry: usize, stack_top: usize) -> Self {
        let mut context = VcpuStateStruct::new();
        context.elr_el2 = entry as u64;
        context.spsr = 0x3C5; // Default PSTATE: EL1h, DAIF masked
        context.vbar_el1 = (entry as u64 + 0x1000) & !0x7FF;
        // context.sp = stack_top as u64;
        
        Self {
            id,
            state: VcpuState::Stopped,
            context,
            entry,
            stack_top,
            pending_irq: false,
            pending_fiq: false,
        }
    }
    
    #[inline]
    pub fn id(&self) -> usize {
        self.id
    }
    
    #[inline]
    pub fn entry_point(&self) -> usize {
        self.entry
    }
    
    #[inline]
    pub fn stack_top(&self) -> usize {
        self.stack_top
    }
    
    #[inline]
    pub fn state(&self) -> VcpuState {
        self.state
    }
    
    #[inline]
    pub fn context(&self) -> &VcpuStateStruct {
        &self.context
    }
    
    #[inline]
    pub fn context_mut(&mut self) -> &mut VcpuStateStruct {
        &mut self.context
    }

    #[inline]
    pub fn pending_irq(&self) -> bool {
        self.pending_irq
    }

    #[inline]
    pub fn pending_fiq(&self) -> bool {
        self.pending_fiq
    }

    #[inline]
    pub fn set_pending_irq(&mut self, val: bool) {
        self.pending_irq = val;
    }

    #[inline]
    pub fn set_pending_fiq(&mut self, val: bool) {
        self.pending_fiq = val;
    }
    
    #[inline]
    pub fn elr(&self) -> u64 {
        self.context.elr_el2
    }
    
    #[inline]
    pub fn set_entry(&mut self, entry: usize) {
        self.entry = entry;
    }
    
    #[inline]
    pub fn set_stack_top(&mut self, stack_top: usize) {
        self.stack_top = stack_top;
    }
    
    #[inline]
    pub fn set_state(&mut self, state: VcpuState) {
        self.state = state;
    }
    
    pub fn prepare_run(&mut self) {
        if self.state == VcpuState::Stopped {
            #[cfg(not(test))]
            vgic::cpu_init(self.id);
        }
        self.state = VcpuState::Running;
    }
    
    pub fn inject_irq(&mut self) {
        self.pending_irq = true;
        let hcr = read_hcr_el2();
        write_hcr_el2(hcr | HCR_EL2_VI);

        unsafe{
            core::arch::asm!("isb", options(nomem, nostack));
        }
    }

    pub fn inject_fiq(&mut self) {
        self.pending_fiq = true;
        let hcr = read_hcr_el2();
        write_hcr_el2(hcr | HCR_EL2_VF);

        unsafe{
            core::arch::asm!("isb", options(nomem, nostack));
        }
    }

    #[inline]
    pub fn can_run(&self) -> bool {
        self.state == VcpuState::Stopped || 
        self.state == VcpuState::Paused ||
        self.state == VcpuState::Exited
    }
}

#[repr(align(16))]
pub struct VcpuManager {
    vcpus: [Option<Vcpu>; 4],
    count: usize,
    current_vcpu: Option<usize>,
    // Store host context, we change elr_el2 to make "eret" return guest.
    pub host_elr: u64,
    pub host_sp: u64,
    pub host_spsr: u64,
    pub host_regs: [u64; 31],
    pub host_vbar: u64,
    pub host_ttbr0: u64,
    pub host_ttbr1: u64,
    pub host_tcr: u64,
    pub host_mair: u64,
    pub host_sctlr: u64,
}

impl VcpuManager {
    #[inline]
    pub const fn new() -> Self {
        Self {
            vcpus: [None, None, None, None],
            count: 0,
            current_vcpu: None,
            host_elr: 0,
            host_sp: 0,
            host_spsr: 0,
            host_regs: [0; 31],
            host_vbar: 0,
            host_ttbr0: 0,
            host_ttbr1: 0,
            host_tcr: 0,
            host_mair: 0,
            host_sctlr: 0,
        }
    }
    
    pub fn create_vcpu(
        &mut self, 
        id: usize, 
        entry: usize, 
        stack_top: usize
    ) -> Result<&mut Vcpu, &'static str> {
        if id >= 4 {
            return Err("vCPU ID out of range (max 3)");
        }

        // Temporary check for max vCPU count
        if self.count >= 4 {
            return Err("Reached max vCPU count");
        }
        
        if self.vcpus[id].is_some() {
            return Err("vCPU ID already used");
        }
        
        let vcpu = Vcpu::new(id, entry, stack_top);
        self.vcpus[id] = Some(vcpu);
        self.count += 1;
        
        Ok(self.vcpus[id].as_mut().unwrap())
    }
    
    pub fn clear_current_vcpu(&mut self) {
        self.current_vcpu = None;
    }
    
    #[inline]
    pub fn get_vcpu(&mut self, id: usize) -> Option<&mut Vcpu> {
        self.vcpus[id].as_mut()
    }
    
    #[inline]
    pub fn current_vcpu_id(&self) -> Option<usize> {
        self.current_vcpu
    }

    #[inline]
    pub fn set_current_vcpu(&mut self, id: usize) {
        self.current_vcpu = Some(id);
    }
    
    #[inline]
    pub fn vcpu_count(&self) -> usize {
        self.count
    }
    
    #[inline]
    pub fn has_running(&self) -> bool {
        self.current_vcpu.is_some()
    }
    
    pub fn iter(&mut self) -> impl Iterator<Item = (usize, &mut Vcpu)> {
        self.vcpus
            .iter_mut()
            .enumerate()
            .filter_map(|(id, vcpu)| vcpu.as_mut().map(|v| (id, v)))
    }
}

#[derive(Debug)]
pub enum VcpuError {
    IdOutOfRange,
    MaxLimitReached,
    IdAlreadyUsed,
    NotFound,
    InvalidState,
}

impl core::fmt::Display for VcpuError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            VcpuError::IdOutOfRange => 
                write!(f, "vCPU ID out of range (max 3)"),
            VcpuError::MaxLimitReached => 
                write!(f, "Reached max vCPU count"),
            VcpuError::IdAlreadyUsed => 
                write!(f, "vCPU ID already used"),
            VcpuError::NotFound => 
                write!(f, "vCPU not found"),
            VcpuError::InvalidState => 
                write!(f, "vCPU state invalid for this operation"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn test_vcpu_state_struct_lifecycle() {
        let mut state = VcpuStateStruct::new();
        assert!(!state.is_valid());

        state.set_elr(0x4000_0000);
        state.sp = 0x4100_0000;
        assert!(state.is_valid());

        state.set_spsr(0x3C5);
        assert_eq!(state.spsr(), 0x3C5);

        state.reset();
        assert_eq!(state.elr(), 0);
        assert!(!state.is_valid());
    }

    #[test]
    fn test_vcpu_manager_allocation() {
        let mut manager = VcpuManager::new();
        assert_eq!(manager.vcpu_count(), 0);
        assert!(!manager.has_running());

        let vcpu0 = manager.create_vcpu(0, 0x4000_0000, 0x4100_0000).expect("Failed to create vCPU 0");
        assert_eq!(vcpu0.id(), 0);
        assert_eq!(vcpu0.entry_point(), 0x4000_0000);
        assert_eq!(vcpu0.state(), VcpuState::Stopped);

        let err_duplicate = manager.create_vcpu(0, 0x4000_0000, 0x4100_0000);
        assert!(err_duplicate.is_err(), "Should not allow duplicate vCPU ID");

        let err_out_of_bounds = manager.create_vcpu(4, 0x4000_0000, 0x4100_0000);
        assert!(err_out_of_bounds.is_err(), "Should reject ID >= MAX_VCPUS");

        manager.create_vcpu(1, 0x4000_0000, 0x4100_0000).unwrap();
        manager.create_vcpu(2, 0x4000_0000, 0x4100_0000).unwrap();
        manager.create_vcpu(3, 0x4000_0000, 0x4100_0000).unwrap();
        assert_eq!(manager.vcpu_count(), 4);
    }

    #[test]
    fn test_vcpu_context_switch_preparation() {
        let mut manager = VcpuManager::new();
        manager.create_vcpu(0, 0x4000_0000, 0x4100_0000).unwrap();
        
        let vcpu = manager.get_vcpu(0).unwrap();
        assert!(vcpu.can_run());
        
        vcpu.prepare_run();
        assert_eq!(vcpu.state(), VcpuState::Running);
        assert!(!vcpu.can_run(), "Running vCPU should not be marked as can_run to prevent re-entry");
    }
}