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

use crate::{
    allocator,
    arch::{
        self,
        riscv::{local_irq_enabled, trap_entry, Context},
    },
    devices::clock::{riscv_clock::RiscvClock, Clock},
    drivers::msip::Msip,
    scheduler, time,
    time::Tick,
    types::Arc,
};
use alloc::{
    alloc::{alloc as system_alloc, dealloc as system_dealloc},
    string::String,
};
use blueos_driver::pinctrl::gd32_af::{AfioMode, Gd32Alterfunc, OutputSpeed, OutputType, PullMode};

pub type ClockImpl = RiscvClock<0xD1000000, 0xD1000008, 40_000_000>;

type Handler = unsafe extern "C" fn();

#[repr(C, align(64))]
struct Vector<const N: usize>([Handler; N]);

impl<const N: usize> Vector<N> {
    pub const fn new() -> Self {
        Self([const { trap_entry }; N])
    }

    pub const fn set(&mut self, index: usize, h: Handler) -> &mut Self {
        self.0[index] = h;
        self
    }
}

#[used]
static mut VECTOR: Vector<{ 116usize }> = Vector::new();

#[inline]
pub fn current_cpu_cycles() -> u64 {
    let hi: u32;
    let lo: u32;
    unsafe {
        core::arch::asm!(
            "rdcycle {lo}",
            "rdcycleh {hi}",
            hi = out(reg) hi,
            lo = out(reg) lo,
            options(nostack, nomem),
        )
    }
    ((hi as u64) << 32) + lo as u64
}

pub(crate) fn handle_plic_irq(ctx: &Context, mcause: usize, mtval: usize) {
    todo!()
}

#[inline]
fn init_vector_table() {
    unsafe {
        core::arch::asm!(
            "la {x}, {trap_entry}",
            "csrw mtvec, {x}",
            "la {x}, {vector}",
            // Inline assembler is unable to encode mtvt, use the numeric value of mtvt here.
            "csrw 0x307, {x}",
            x = out(reg) _,
            trap_entry = sym trap_entry,
            vector = sym VECTOR,
            options(nostack),
        );
    }
}

pub(crate) fn handle_irq(_ctx: &Context, _mcause: usize, _mtval: usize) {
    let irq_number: usize;
    unsafe {
        core::arch::asm!(
            // // Inline assembler is unable to encode mnxti, use the numeric value of mnxti here.
            "csrr {}, 0x345",
            out(reg) irq_number,
            options(nostack),
        )
    }
}

unsafe fn copy_data() {
    extern "C" {
        static __data_lma: u8;
        static mut __data_start: u8;
        static mut __data_end: u8;
    }
    let src = core::ptr::addr_of!(__data_lma);
    let dst = core::ptr::addr_of_mut!(__data_start);
    let size = core::ptr::addr_of_mut!(__data_end).offset_from(dst as *const _) as usize;
    core::ptr::copy_nonoverlapping(src, dst, size)
}

pub(crate) fn init() {
    debug_assert!(!local_irq_enabled());
    unsafe { copy_data() };
    crate::boot::init_runtime();
    use blueos_hal::clock_control::ClockControl;
    blueos_driver::clock_control::gd32_clock_control::Gd32ClockControl::init();
    crate::boot::init_heap();
    init_vector_table();
    ClockImpl::stop();
}

crate::define_peripheral! {
    (console_uart, blueos_driver::uart::gd32vw55x::Gd32vw55xUart,
    blueos_driver::uart::gd32vw55x::Gd32vw55xUart::new(
        0x4000_4800
    ))
}

crate::define_pin_states!(
    Gd32Alterfunc,
    (
        0x4002_0400,
        15,
        PullMode::PullUp,
        AfioMode::Af8,
        OutputType::PushPull,
        OutputSpeed::Medium,
    ),
    (
        0x4002_0000,
        8,
        PullMode::PullUp,
        AfioMode::Af2,
        OutputType::PushPull,
        OutputSpeed::Medium,
    ),
);

// Used by many drivers in gd32's SDK.
#[no_mangle]
pub extern "C" fn delay_1ms(millis: u32) {
    let ticks = Tick::from_millis(millis as u64);
    if ticks == Tick(0) {
        scheduler::yield_me()
    } else {
        scheduler::suspend_me_for::<()>(ticks, None);
    }
}

type MyMsip = Msip<0xD1000000>;

#[inline(always)]
pub(crate) fn send_ipi(hart: usize) {
    MyMsip::send_ipi(hart)
}

#[inline(always)]
pub(crate) fn clear_ipi(hart: usize) {
    MyMsip::clear_ipi(hart)
}
