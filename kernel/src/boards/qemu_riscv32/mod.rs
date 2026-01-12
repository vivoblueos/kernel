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
use crate::{
    arch,
    arch::riscv::{local_irq_enabled, trap_entry, Context},
    devices::clock::Clock,
    drivers::{ic::plic::Plic, msip::Msip},
    scheduler,
    support::SmpStagedInit,
    time,
};
use core::sync::atomic::Ordering;
pub(crate) static PLIC: Plic = Plic::new(config::PLIC_BASE);
pub use crate::devices::clock::riscv_clock::QemuRiscvClock as ClockImpl;

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

pub(crate) fn handle_plic_irq(ctx: &Context, mcause: usize, mtval: usize) {
    let cpu_id = arch::current_cpu_id();
    PLIC.complete(cpu_id, PLIC.claim(cpu_id))
}

static STAGING: SmpStagedInit = SmpStagedInit::new();

pub(crate) fn init() {
    assert!(!local_irq_enabled());
    STAGING.run(0, true, crate::boot::init_runtime);
    STAGING.run(1, true, crate::boot::init_heap);
    STAGING.run(2, false, init_vector_table);
    STAGING.run(3, false, ClockImpl::stop);
    // From now on, all work will be done by core 0.
    if arch::current_cpu_id() != 0 {
        scheduler::wait_and_then_start_schedule();
        unreachable!("Secondary cores should have jumped to the scheduler");
    }
    // Enable UART0 in PLIC.
    PLIC.enable(
        arch::current_cpu_id(),
        u32::try_from(usize::from(config::UART0_IRQ))
            .expect("usize(64 bits) converts to u32 failed"),
    );
    // Set UART0 priority in PLIC.
    PLIC.set_priority(
        u32::try_from(usize::from(config::UART0_IRQ))
            .expect("usize(64 bits) converts to u32 failed"),
        1,
    );
}

crate::define_peripheral! {
    (console_uart, blueos_driver::uart::dumb::DumbUart,
     blueos_driver::uart::dumb::DumbUart),
}

crate::define_pin_states!(None);

type MyMsip = Msip<0x0200_0000>;

#[inline(always)]
pub(crate) fn send_ipi(hart: usize) {
    MyMsip::send_ipi(hart)
}

#[inline(always)]
pub(crate) fn clear_ipi(hart: usize) {
    MyMsip::clear_ipi(hart)
}
