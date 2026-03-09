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

use core::ptr::addr_of;
use cortex_m::peripheral::{MPU, SCB};

const MPU_CTRL_ENABLE: u32 = 1 << 0;
const MPU_CTRL_PRIVDEFENA: u32 = 1 << 2;
const MPU_REGION_GUARD: u32 = 0;
const MPU_RBAR_XN: u32 = 1 << 0;
// AP=0b10: privileged read-only, unprivileged no access.
const MPU_RBAR_AP_PRIV_RO: u32 = 0b10 << 1;
const MPU_RLAR_REGION_ENABLE: u32 = 1 << 0;
const SCB_SHCSR_MEMFAULTENA: u32 = 1 << 16;

extern "C" {
    static __sys_stack_guard_start: u8;
    static __sys_stack_guard_end: u8;
}

#[inline]
fn barrier() {
    unsafe {
        core::arch::asm!("dsb", "isb", options(nostack, preserves_flags));
    }
}

#[inline]
fn encode_rbar(base: usize) -> u32 {
    ((base as u32) & !0x1f) | MPU_RBAR_AP_PRIV_RO | MPU_RBAR_XN
}

#[inline]
fn encode_rlar(end: usize) -> u32 {
    debug_assert!(end >= 32);
    (((end - 1) as u32) & !0x1f) | MPU_RLAR_REGION_ENABLE
}

pub fn init_sys_stack_guard() {
    let guard_start = addr_of!(__sys_stack_guard_start) as usize;
    let guard_end = addr_of!(__sys_stack_guard_end) as usize;
    debug_assert!(guard_end > guard_start);
    debug_assert_eq!(guard_start & 0x1f, 0);
    debug_assert_eq!(guard_end & 0x1f, 0);

    let mpu = unsafe { &*MPU::PTR };
    let scb = unsafe { &*SCB::PTR };

    let mut ctrl = mpu.ctrl.read();
    ctrl &= !MPU_CTRL_ENABLE;
    unsafe { mpu.ctrl.write(ctrl) };
    barrier();

    unsafe {
        mpu.rnr.write(MPU_REGION_GUARD);
        mpu.rbar.write(encode_rbar(guard_start));
        mpu.rlar.write(encode_rlar(guard_end));
    }

    // Keep background memory map for privileged code and enable MPU faulting.
    unsafe { mpu.ctrl.write(MPU_CTRL_ENABLE | MPU_CTRL_PRIVDEFENA) };
    let mut shcsr = scb.shcsr.read();
    shcsr |= SCB_SHCSR_MEMFAULTENA;
    unsafe { scb.shcsr.write(shcsr) };
    barrier();
}
