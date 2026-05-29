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

pub mod exit;
pub mod guest;
pub mod hyper;
pub mod mmu_el2;
pub mod mmu_s2;
pub mod vcpu;
pub mod vector;
pub mod vgic;
pub mod vtimer;
pub mod vuart;
pub(crate) mod virtio;
pub use crate::arch::aarch64::psci::hvc_call;
use blueos_hal::{PlatPeri, isr::IsrDesc};
pub use exit::{VmExitInfo, VmExitReason};
pub use hyper::{get_current_el, hyp_init};
pub use vcpu::{Vcpu, VcpuManager, VcpuState};
pub use vgic::init;

use crate::{kearly_println, kprintln};

#[no_mangle]
pub extern "C" fn hyper_trap_irq(_context: &mut crate::arch::aarch64::Context) -> usize {
    unsafe {
        let mut ctlr: u64;
        core::arch::asm!("mrs {}, ICC_CTLR_EL1", out(reg) ctlr);
        if (ctlr & (1 << 1)) == 0 {
            // set EOImode.
            ctlr |= 1 << 1;
            core::arch::asm!("msr ICC_CTLR_EL1, {}", in(reg) ctlr);
            core::arch::asm!("isb");
        }
    }

    let vcpu_id = get_current_vcpu_id().expect("Failed to get current vcpu id");
    vgic::sync(vcpu_id);

    let iar: u64;
    unsafe {
        core::arch::asm!("mrs {}, ICC_IAR1_EL1", out(reg) iar);
    }

    let intid = iar & 0xFFFFFF;

    if intid == 1023 {
        // 1023 is Spurious Interrupt of GIC，skip
        vgic::flush(vcpu_id);
        return 0;
    }

    if intid == 33 {
        vuart::handle_physical_uart_interrupt();
        vgic::flush(vcpu_id);

        unsafe {
            core::arch::asm!("msr ICC_EOIR1_EL1, {}", in(reg) iar);
            core::arch::asm!("msr ICC_DIR_EL1, {}", in(reg) iar);
        }
        return 0;
    } else if intid == 27 {
        let is_enabled = {
            let redist = vgic::get_vgic().redists[vcpu_id].lock();
            (redist.isenabler0 & (1 << 27)) != 0
        };

        if !is_enabled {
            unsafe {
                let mut ctl: u64;
                core::arch::asm!("mrs {}, CNTV_CTL_EL0", out(reg) ctl);
                ctl |= 1 << 1;
                core::arch::asm!("msr CNTV_CTL_EL0, {}", in(reg) ctl);
                core::arch::asm!("msr ICC_EOIR1_EL1, {}", in(reg) iar);
                core::arch::asm!("msr ICC_DIR_EL1, {}", in(reg) iar);
            }
            return 0;
        }

        vgic::inject_irq(vcpu_id, 27);
        vgic::flush(vcpu_id);
        unsafe {
            // For hardware routed timer, we only do EOI (Priority Drop).
            // The guest will automatically do DIR (Deactivate) when it EOIs.
            core::arch::asm!("msr ICC_EOIR1_EL1, {}", in(reg) iar);
        }
        return 0;
    } else {
        kearly_println!("[EL2] Unhandled Guest IRQ: {}", intid);
    }

    unsafe {
        core::arch::asm!("msr ICC_EOIR1_EL1, {}", in(reg) iar);
        core::arch::asm!("msr ICC_DIR_EL1, {}", in(reg) iar);   
    }

    vgic::flush(vcpu_id);
    0
}

#[no_mangle]
pub extern "C" fn hyper_trap_fiq(_context: &mut crate::arch::aarch64::Context) -> usize {
    0
}

#[repr(align(16))]
pub struct VcpuManagerWrapper(pub vcpu::VcpuManager);

pub static mut VCPU_MANAGER: VcpuManagerWrapper = VcpuManagerWrapper(vcpu::VcpuManager::new());

#[inline]
pub fn get_current_vcpu_id() -> Option<usize> {
    unsafe { VCPU_MANAGER.0.current_vcpu_id() }
}

pub fn virt_init() {
    hyp_init();
}

pub fn virt_boot_linux() {
    vgic::init();
    vtimer::init_global_vtimer();

    unsafe {
        let current_el = hyper::get_current_el();
        if current_el == 2 {
            let mut ich_hcr: u64;
            core::arch::asm!("mrs {}, ich_hcr_el2", out(reg) ich_hcr);
            if (ich_hcr & 1) == 0 {
                ich_hcr |= 1;
                core::arch::asm!("msr ich_hcr_el2, {}", in(reg) ich_hcr);
                core::arch::asm!("isb");
            }
        }
    }

    // Initiate vCpu for Linux kernel, set the entry point and parameters.
    unsafe {
        let vcpu = VCPU_MANAGER
            .0
            .create_vcpu(0, guest::LINUX_KERNEL_LOAD_ADDR, 0)
            .unwrap();
        let mut ctx = vcpu.context_mut();
        ctx.regs[0] = guest::LINUX_DTB_ADDR as u64;
        ctx.spsr = 0x3C5;
        ctx.sctlr_el1 = 0x30d00800;
    }

    vtimer::init_vcpu_timer();
    vuart::enable_physical_uart_interrupts();
    let result = hvc_call(2, 0, 0);
    vuart::cleanup_physical_uart_interrupts();

    if result == 0 {
        kearly_println!("Linux shutdown!!!");
    }
}
