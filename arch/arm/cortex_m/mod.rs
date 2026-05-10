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

mod boot;
pub mod context;
mod exception;
pub mod irq;

pub use boot::cortex_m_boot_entry;
pub use context::{Context, ExceptionContext, IsrContext};
pub use exception::{handle_pendsv, handle_svc, handle_systick};

#[inline(never)]
pub extern "C" fn switch_context_with_hook(hook: crate::RawContextSwitchHook) {
    // Keep the old Cortex-M scheduler switch ABI: the opaque scheduler hook is
    // passed in r0, r7 carries NR_SWITCH, and SVC routes into handle_svc().
    // bluekernel_arch owns the register convention while kernel policy remains
    // behind the raw callback used by the exception handler.
    unsafe {
        core::arch::asm!(
            "movs {tmp}, r7",
            "ldr r7, ={nr}",
            "svc 0",
            "mov r7, {tmp}",
            in("r0") hook as usize,
            tmp = out(reg) _,
            nr = const exception::NR_SWITCH,
            options(nostack),
        )
    }
}

#[inline(always)]
pub extern "C" fn restore_context_with_hook(hook: crate::RawContextSwitchHook) -> ! {
    switch_context_with_hook(hook);
    unreachable!("Should have switched to another thread");
}

#[naked]
pub extern "C" fn switch_stack(to_sp: usize, cont: crate::StackSwitchContinuation) -> ! {
    // This is the old kernel-side signal stack trampoline moved verbatim:
    // capture the current PSP in r1, install the target PSP from r0, and jump
    // to the continuation held in r1/r12. The continuation still belongs to
    // kernel policy; only the PSP register dance lives here.
    unsafe {
        core::arch::naked_asm!(
            "
            mov r12, r1
            mrs r1, psp
            msr psp, r0
            bx r12
            "
        )
    }
}
