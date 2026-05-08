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

use super::{guest, hyper, vcpu::Vcpu, vgic};
use core::arch::asm;
#[cfg(test)]
use semihosting::println;

static mut GUEST_SHUTDOWN: bool = false;

pub const PSCI_VERSION: u32 = 0x8400_0000;
pub const PSCI_SYSTEM_OFF: u32 = 0x8400_0008;
pub const PSCI_SYSTEM_RESET: u32 = 0x8400_0009;
pub const PSCI_FEATURES: u32 = 0x8400_000A;
pub const HVC_VMM_GET_INFO: u64 = 0x11;
pub const HVC_VMM_INJECT_IRQ: u64 = 0x13;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum VmExitReason {
    Hvc,
    Svc,
    DataAbortLowerEL,
    InstructionAbortLowerEL,
    TrappedWfiWfe,
    Unknown(u32),
}

#[derive(Debug)]
pub struct VmExitInfo {
    pub reason: VmExitReason,
    pub esr: u64,
    pub far: usize,
    pub pstate: u64,
    pub return_addr: usize,
}

#[inline]
pub fn parse_exit_reason(esr: u64) -> VmExitReason {
    let ec = (esr >> 26) & 0x3F;

    match ec {
        0x16 | 0x17 => VmExitReason::Hvc,
        0x15 => VmExitReason::Svc,
        0x24 => VmExitReason::DataAbortLowerEL,
        0x20 => VmExitReason::InstructionAbortLowerEL,
        0x01 => VmExitReason::TrappedWfiWfe,
        _ => VmExitReason::Unknown(ec as u32),
    }
}

pub fn handle_vm_exit(vcpu: &mut Vcpu) -> bool {
    vgic::sync(vcpu.id());
    let _context = vcpu.context_mut();
    let esr = read_esr_el2();
    let elr = read_elr_el2();
    let pstate = read_spsr_el2();
    let reason = parse_exit_reason(esr);

    let exit_info = VmExitInfo {
        reason,
        esr,
        far: elr,
        pstate,
        return_addr: elr + 4,
    };

    match reason {
        VmExitReason::Hvc => handle_hvc(vcpu, &exit_info),
        VmExitReason::Svc => handle_svc(vcpu, &exit_info),
        VmExitReason::DataAbortLowerEL => {
            let iss = esr & 0x1FFFFFF;
            let dfsc = iss & 0x3F;
            let is_write = (iss & (1 << 6)) != 0;
            let faulting_pc = vcpu.context().elr_el2;

            if (dfsc & 0x3C) == 0x04 || (dfsc & 0x3C) == 0x08 || (dfsc & 0x3C) == 0x0C {
                // Translation fault (level 0/1/2/3) - Stage-2 未映射
                unsafe {
                    let far: u64;
                    core::arch::asm!("mrs {}, far_el2", out(reg) far, options(nostack));
                    let hpfar_el2: u64;
                    core::arch::asm!("mrs {}, hpfar_el2", out(reg) hpfar_el2, options(nostack));
                    //Caculate exact PA for vGIC.
                    let fault_ipa_base = (hpfar_el2 & 0x0000_00FF_FFFF_FFF0) << 8;
                    let exact_ipa = fault_ipa_base | (far & 0xFFF);
                    let handled = vgic::handle_data_abort(
                        vcpu.id(),
                        esr,
                        exact_ipa,
                        &mut vcpu.context_mut().regs,
                    );

                    if handled {
                        vcpu.context_mut().elr_el2 += 4;
                        vgic::flush(vcpu.id());
                        return true;
                    } else {
                        #[cfg(test)]
                        semihosting::println!("[EXIT]   Unhandled Stage-2 Address!");
                    }
                }
            }
            false
        }
        VmExitReason::InstructionAbortLowerEL => {
            let iss = esr & 0x1FFFFFF;
            let ifsc = iss & 0x3F;
            false
        }
        VmExitReason::TrappedWfiWfe => {
            let iss = exit_info.esr & 0x1FFFFFF;
            let is_wfe = (iss & 1) != 0;
            vcpu.context_mut().elr_el2 += 4;

            if is_wfe {
                true
            } else {
                let irq_masked = (vcpu.context().spsr & (1 << 7)) != 0;

                if irq_masked {
                    false
                } else {
                    unsafe {
                        core::arch::asm!("wfi");
                    }
                    true
                }
            }
        }
        VmExitReason::Unknown(ec) => {
            #[cfg(test)]
            semihosting::println!("[EXIT]  Unknown Exit Reason: EC = {:#x}", ec);
            false
        }
    }
}

// hvc from guest.
fn handle_hvc(vcpu: &mut Vcpu, info: &VmExitInfo) -> bool {
    let saved_x0 = vcpu.context().regs[0];
    let vcpu_id = vcpu.id();
    let context = vcpu.context_mut();
    let hvc_num = info.esr & 0xFFFF;
    let mut need_advance_pc = true;
    let mut is_psci_call = false;

    // Easy HVC Services.
    let result = match hvc_num {
        0x00 => {
            let psci_func_id = context.regs[0] as u32;
            is_psci_call = true;

            match psci_func_id {
                PSCI_VERSION => {
                    let version = 0x0000_0002;
                    context.regs[0] = version;
                }
                PSCI_SYSTEM_OFF | PSCI_SYSTEM_RESET => {
                    unsafe {
                        GUEST_SHUTDOWN = true;
                    }
                    need_advance_pc = false;
                    return false;
                }
                PSCI_FEATURES => {
                    let feature_id = context.regs[1] as u32;
                    if feature_id == PSCI_SYSTEM_OFF || feature_id == PSCI_SYSTEM_RESET {
                        context.regs[0] = 0;
                    } else {
                        context.regs[0] = 0xFFFF_FFFF;
                    }
                }
                _ => {
                    #[cfg(test)]
                    semihosting::println!("[EXIT] HVC#0: Ignored PSCI call: {:#x}", psci_func_id);
                    context.regs[0] = 0xFFFF_FFFF;
                }
            }

            true
        }
        HVC_VMM_GET_INFO => {
            context.regs[0] = 0x48495001;
            true
        }
        _ => {
            #[cfg(test)]
            semihosting::println!("[EXIT]   Unknown HVC Number");
            true
        }
    };

    if result && need_advance_pc {
        context.elr_el2 += 4;
    }

    result
}

// To DO: Finish this function.
fn handle_svc(vcpu: &mut Vcpu, info: &VmExitInfo) -> bool {
    let context = vcpu.context_mut();
    let svc_num = context.regs[0];

    match svc_num {
        0 => {
            context.regs[0] = 0;
        }
        1 => {
            context.regs[0] = 1;
        }
        _ => {
            context.regs[0] = 0xFFFFFFFF;
        }
    }

    context.elr_el2 = info.return_addr as u64;
    true
}

pub fn is_guest_shutdown() -> bool {
    unsafe { GUEST_SHUTDOWN }
}

pub fn clear_guest_shutdown() {
    unsafe {
        GUEST_SHUTDOWN = false;
    }
}

#[inline]
fn read_esr_el2() -> u64 {
    let esr: u64;
    unsafe {
        asm!("mrs {}, esr_el2", out(reg) esr, options(nostack));
    }
    esr
}

#[inline]
fn read_elr_el2() -> usize {
    let elr: usize;
    unsafe {
        asm!("mrs {}, elr_el2", out(reg) elr, options(nostack));
    }
    elr
}

#[inline]
fn read_spsr_el2() -> u64 {
    let spsr: u64;
    unsafe {
        asm!("mrs {}, spsr_el2", out(reg) spsr, options(nostack));
    }
    spsr
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn test_parse_exit_reason_exhaustive() {
        assert_eq!(parse_exit_reason(0x16 << 26), VmExitReason::Hvc);
        assert_eq!(parse_exit_reason(0x15 << 26), VmExitReason::Svc);
        assert_eq!(
            parse_exit_reason(0x24 << 26),
            VmExitReason::DataAbortLowerEL
        );
        assert_eq!(
            parse_exit_reason(0x20 << 26),
            VmExitReason::InstructionAbortLowerEL
        );
        assert_eq!(parse_exit_reason(0x01 << 26), VmExitReason::TrappedWfiWfe);
    }

    #[test]
    fn test_handle_hvc_pc_increment_and_psci() {
        let mut vcpu = Vcpu::new(0, 0x4000_0000, 0x4100_0000);
        let initial_pc = 0x4000_1000;

        // Scenario 1: HVC #0x11 (Get Information), should resume execution and PC + 4
        vcpu.context_mut().elr_el2 = initial_pc;
        let info_normal = VmExitInfo {
            reason: VmExitReason::Hvc,
            esr: (0x16 << 26) | 0x11,
            far: 0,
            pstate: 0,
            return_addr: initial_pc as usize + 4,
        };
        let should_resume = handle_hvc(&mut vcpu, &info_normal);
        assert!(should_resume);
        assert_eq!(
            vcpu.context().regs[0],
            0x48495001,
            "Should set magic return value"
        );
        assert_eq!(
            vcpu.context().elr_el2,
            initial_pc + 4,
            "PC MUST be incremented to avoid infinite loop!"
        );

        // Scenario 2: PSCI SYSTEM OFF (HVC #0, X0 = 0x84000008), should shut down and refuse recovery.
        vcpu.context_mut().elr_el2 = initial_pc;
        vcpu.context_mut().regs[0] = 0x84000008;
        // EC = 0x16, ISS = 0x00
        let info_shutdown = VmExitInfo {
            reason: VmExitReason::Hvc,
            esr: (0x16 << 26),
            far: 0,
            pstate: 0,
            return_addr: initial_pc as usize + 4,
        };
        clear_guest_shutdown();
        let should_resume_shutdown = handle_hvc(&mut vcpu, &info_shutdown);
        assert!(
            !should_resume_shutdown,
            "Should refuse to resume on PSCI Shutdown"
        );
        assert!(is_guest_shutdown(), "Global shutdown flag must be set");
        assert_eq!(vcpu.context().elr_el2, initial_pc);
    }
}
