// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
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

// This code is based on
// https://github.com/eclipse-threadx/threadx/blob/master/ports/risc-v64/gnu/example_build/qemu_virt/hwtimer.c
// https://github.com/eclipse-threadx/threadx/blob/master/ports/risc-v64/gnu/example_build/qemu_virt/trap.c
// https://github.com/eclipse-threadx/threadx/blob/master/ports/risc-v64/gnu/example_build/qemu_virt/uart.c
// Copyright (c) 2024 - present Microsoft Corporation
// SPDX-License-Identifier: MIT

mod config;
mod uart;
use crate::{
    arch,
    arch::riscv::{local_irq_enabled, trap_entry, Context},
    devices::{console, dumb, Device, DeviceManager},
    drivers::ic::plic::Plic,
    scheduler,
    support::SmpStagedInit,
    time,
};
use alloc::string::String;
use core::sync::atomic::Ordering;
pub(crate) use uart::get_early_uart;
pub(crate) static PLIC: Plic = Plic::new(config::PLIC_BASE);

const CLOCK_ADDR: usize = 0x0200_0000;
const CLOCK_TIME: usize = CLOCK_ADDR + 0xBFF8;
const CLOCK_HZ: u64 = 10_000_000;
const CLOCK_PERIOD_NANOS: u64 = 1_000_000_000 / CLOCK_HZ;

#[inline]
fn clock_timecmp_ptr(hart: usize) -> *mut u64 {
    unsafe { (CLOCK_ADDR + 0x4000 + 8 * hart) as *mut u64 }
}

#[inline]
pub fn current_clock_cycles() -> u64 {
    unsafe { (CLOCK_TIME as *const u64).read_volatile() }
}

#[inline]
pub fn current_cpu_cycles() -> u64 {
    let x: u64;
    unsafe {
        core::arch::asm!(
            "rdcycle {}",
            out(reg) x,
            options(nostack, nomem),
        )
    }
    x
}

fn set_timecmp(deadline: u64) {
    let hart = arch::current_cpu_id();
    unsafe { clock_timecmp_ptr(hart).write_volatile(deadline) };
}

#[inline]
fn init_vector_table() {
    unsafe {
        core::arch::asm!(
            "la {x}, {entry}",
            "csrw mtvec, {x}",
            x = out(reg) _,
            entry = sym trap_entry,
            options(nostack),
        );
    }
}

pub(crate) fn handle_irq(ctx: &Context, mcause: usize, mtval: usize) {
    let cpu_id = arch::current_cpu_id();
    PLIC.complete(cpu_id, PLIC.claim(cpu_id))
}

#[inline]
pub(crate) fn set_timeout_after_nanos(nanos: u64) {
    set_timecmp(current_clock_cycles() + nanos / CLOCK_PERIOD_NANOS);
}

#[inline]
pub(crate) fn clock_cycles_to_millis(interval: u64) -> u64 {
    interval * CLOCK_PERIOD_NANOS / 1_000_000
}

#[inline]
pub(crate) fn clock_cycles_to_duration(cycles: u64) -> core::time::Duration {
    core::time::Duration::from_nanos(cycles * CLOCK_PERIOD_NANOS)
}

#[inline]
pub(crate) fn uptime() -> core::time::Duration {
    clock_cycles_to_duration(current_clock_cycles())
}

static STAGING: SmpStagedInit = SmpStagedInit::new();

pub(crate) fn init() {
    assert!(!local_irq_enabled());
    STAGING.run(0, true, crate::boot::init_runtime);
    STAGING.run(1, true, crate::boot::init_heap);
    STAGING.run(2, false, init_vector_table);
    STAGING.run(3, true, || {
        time::systick_init(0);
    });
    STAGING.run(4, false, time::reset_systick);
    // From now on, all work will be done by core 0.
    if arch::current_cpu_id() != 0 {
        scheduler::wait_and_then_start_schedule();
        unreachable!("Secondary cores should have jumped to the scheduler");
    }
    enumerate_devices();
    // FIXME: It's weird we use VFS before it's initialized.
    register_devices_in_vfs();
    crate::boot::init_vfs();
}

fn enumerate_devices() {
    uart::uart_init(0);
}

fn register_devices_in_vfs() {
    console::init_console(dumb::get_serial0().clone());
    DeviceManager::get().register_device(String::from("ttyS0"), dumb::get_serial0().clone());
}
