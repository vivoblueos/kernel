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

pub use bluekernel_arch::interface::*;

#[cfg(target_arch = "arm")]
pub mod arm;
#[cfg(target_arch = "arm")]
pub use arm::*;

#[cfg(any(target_arch = "riscv64", target_arch = "riscv32"))]
pub mod riscv;
#[cfg(any(target_arch = "riscv64", target_arch = "riscv32"))]
pub use riscv::*;

#[cfg(target_arch = "aarch64")]
pub mod aarch64;
#[cfg(target_arch = "aarch64")]
pub use aarch64::*;
#[cfg(target_arch = "aarch64")]
pub type IsrContext = aarch64::Context;

#[allow(dead_code)]
pub(crate) struct KernelArch;

#[cfg(target_arch = "arm")]
impl ThreadContext for arm::Context {
    fn init(&mut self) -> &mut Self {
        arm::Context::init(self)
    }

    fn set_return_address(&mut self, address: usize) -> &mut Self {
        arm::Context::set_return_address(self, address)
    }

    fn set_arg(&mut self, index: usize, value: usize) -> &mut Self {
        arm::Context::set_arg(self, index, value)
    }
}

#[cfg(target_arch = "arm")]
impl ArchInterface for KernelArch {
    type Context = arm::Context;
    type IsrContext = arm::IsrContext;

    fn disable_local_irq() {
        arm::disable_local_irq();
    }

    fn enable_local_irq() {
        arm::enable_local_irq();
    }

    fn disable_local_irq_save() -> IrqState {
        arm::disable_local_irq_save()
    }

    fn enable_local_irq_restore(old: IrqState) {
        arm::enable_local_irq_restore(old);
    }

    fn local_irq_enabled() -> bool {
        arm::local_irq_enabled()
    }

    fn current_cpu_id() -> CpuId {
        arm::current_cpu_id()
    }

    fn current_sp() -> usize {
        arm::current_sp()
    }

    fn idle() {
        arm::idle();
    }

    fn start_schedule(cont: ScheduleEntry) {
        arm::start_schedule(cont);
    }

    fn pend_switch_context() {
        arm::pend_switch_context();
    }

    fn switch_context_with_hook(hook: RawContextSwitchHook) {
        arm::switch_context_with_hook(hook.cast());
    }

    fn restore_context_with_hook(hook: RawContextSwitchHook) -> ! {
        arm::restore_context_with_hook(hook.cast())
    }

    fn switch_stack(to_sp: usize, cont: StackSwitchContinuation) -> ! {
        arm::switch_stack(to_sp, cont)
    }
}

#[cfg(any(target_arch = "riscv64", target_arch = "riscv32"))]
impl ThreadContext for riscv::Context {
    fn init(&mut self) -> &mut Self {
        riscv::Context::init(self)
    }

    fn set_return_address(&mut self, address: usize) -> &mut Self {
        riscv::Context::set_return_address(self, address)
    }

    fn set_arg(&mut self, index: usize, value: usize) -> &mut Self {
        riscv::Context::set_arg(self, index, value)
    }
}

#[cfg(any(target_arch = "riscv64", target_arch = "riscv32"))]
impl ArchInterface for KernelArch {
    type Context = riscv::Context;
    type IsrContext = riscv::IsrContext;

    fn disable_local_irq() {
        riscv::disable_local_irq();
    }

    fn enable_local_irq() {
        riscv::enable_local_irq();
    }

    fn disable_local_irq_save() -> IrqState {
        riscv::disable_local_irq_save()
    }

    fn enable_local_irq_restore(old: IrqState) {
        riscv::enable_local_irq_restore(old);
    }

    fn local_irq_enabled() -> bool {
        riscv::local_irq_enabled()
    }

    fn current_cpu_id() -> CpuId {
        riscv::current_cpu_id()
    }

    fn current_sp() -> usize {
        riscv::current_sp()
    }

    fn idle() {
        riscv::idle();
    }

    fn start_schedule(cont: ScheduleEntry) {
        riscv::start_schedule(cont);
    }

    fn pend_switch_context() {
        riscv::pend_switch_context();
    }

    fn switch_context_with_hook(hook: RawContextSwitchHook) {
        riscv::switch_context_with_hook(hook.cast());
    }

    fn restore_context_with_hook(hook: RawContextSwitchHook) -> ! {
        riscv::restore_context_with_hook(hook.cast())
    }

    fn switch_stack(to_sp: usize, cont: StackSwitchContinuation) -> ! {
        riscv::switch_stack(to_sp, cont)
    }
}

#[cfg(target_arch = "aarch64")]
impl ThreadContext for aarch64::Context {
    fn init(&mut self) -> &mut Self {
        aarch64::Context::init(self)
    }

    fn set_return_address(&mut self, address: usize) -> &mut Self {
        aarch64::Context::set_return_address(self, address)
    }

    fn set_arg(&mut self, index: usize, value: usize) -> &mut Self {
        aarch64::Context::set_arg(self, index, value)
    }
}

#[cfg(target_arch = "aarch64")]
impl ArchInterface for KernelArch {
    type Context = aarch64::Context;
    type IsrContext = aarch64::Context;

    fn disable_local_irq() {
        aarch64::disable_local_irq();
    }

    fn enable_local_irq() {
        aarch64::enable_local_irq();
    }

    fn disable_local_irq_save() -> IrqState {
        aarch64::disable_local_irq_save()
    }

    fn enable_local_irq_restore(old: IrqState) {
        aarch64::enable_local_irq_restore(old);
    }

    fn local_irq_enabled() -> bool {
        aarch64::local_irq_enabled()
    }

    fn current_cpu_id() -> CpuId {
        aarch64::current_cpu_id()
    }

    fn current_sp() -> usize {
        aarch64::current_sp()
    }

    fn idle() {
        aarch64::idle();
    }

    fn start_schedule(cont: ScheduleEntry) {
        aarch64::start_schedule(cont);
    }

    fn pend_switch_context() {
        aarch64::pend_switch_context();
    }

    fn switch_context_with_hook(hook: RawContextSwitchHook) {
        aarch64::switch_context_with_hook(hook.cast());
    }

    fn restore_context_with_hook(hook: RawContextSwitchHook) -> ! {
        aarch64::restore_context_with_hook(hook.cast())
    }

    fn switch_stack(to_sp: usize, cont: StackSwitchContinuation) -> ! {
        aarch64::switch_stack(to_sp, cont)
    }
}
