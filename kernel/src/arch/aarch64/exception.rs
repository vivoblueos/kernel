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

use super::{Context, NR_SWITCH};
use crate::{
    arch::RawExceptionFrame,
    scheduler::{self, ContextSwitchHookHolder},
};

pub(crate) extern "C" fn prepare_svc_switch_from_raw(frame: RawExceptionFrame) -> usize {
    // This is the old prepare_for_context_switch(context) path. Exception
    // entry now passes an opaque raw frame from bluekernel_arch, but Phase 4
    // has not moved AArch64 Context ownership yet, so the frame is cast back
    // to the kernel Context layout before reading the scheduler hook in x0.
    let context = unsafe { &*frame.cast::<Context>() };
    let hook_ptr = context.x0 as *const ContextSwitchHookHolder;
    let hook = unsafe { &*hook_ptr };
    scheduler::spin_until_ready_to_run(unsafe { hook.next_thread() })
}

pub(crate) extern "C" fn finish_svc_switch_from_raw(
    to: RawExceptionFrame,
    from: RawExceptionFrame,
) -> usize {
    // This is the old AArch64 might_switch() scheduler tail. The exception
    // entry has moved to bluekernel_arch, but ContextSwitchHookHolder remains
    // a kernel scheduler type until Phase 4, so the raw frame is cast back to
    // the kernel-side Context with the same repr(C) layout.
    let from_context = unsafe { &*from.cast::<Context>() };
    debug_assert_eq!(to != from, from_context.x8 == NR_SWITCH);
    if to == from {
        return from as usize;
    }

    let hook_ptr = from_context.x0 as *mut ContextSwitchHookHolder;
    let hook = unsafe { &mut *hook_ptr };
    scheduler::save_context_finish_hook(hook, from as usize)
}

pub(crate) extern "C" fn fatal_trap_from_raw(
    frame: RawExceptionFrame,
    ec: usize,
    _esr: usize,
) -> ! {
    let context = unsafe { &mut *frame.cast::<Context>() };
    show_exception(ec as u64, context)
}

fn show_exception(ec: u64, context: &mut Context) -> ! {
    match ec {
        0x00 => panic!("Unknown reason Exceptions\n======== error stack ======== \n{}",context),
        0x01 => panic!("WFI or WFE instruction\n======== error stack ======== \n{}",context),
        0x03 => panic!("MCR or MRC access to CP15a that is not reported using EC 0x00\n======== error stack ======== \n{}",context),
        0x04 => panic!("MCRR or MRRC access to CP15a that is not reported using EC 0x00\n======== error stack ======== \n{}",context),
        0x05 => panic!("MCR or MRC access to CP14a\n======== error stack ======== \n{}",context),
        0x06 => panic!("LDC or STC access to CP14a\n======== error stack ======== \n{}",context),
        0x07 => panic!("Access to SIMD or floating-point registersa, excluding (HCR_EL2.TGE==1) traps\n======== error stack ======== \n{}",context),
        0x08 => panic!("MCR or MRC access to CP10 that is not reported using EC 0x07. This applies only to ID Group trapsd\n======== error stack ======== \n{}",context),
        0x0c => panic!("MRRC access to CP14a\n======== error stack ======== \n{}",context),
        0x0e => panic!("Illegal Execution State\n======== error stack ======== \n{}",context),
        0x11 => panic!("SVC call from Aarch32\n======== error stack ======== \n{}",context),
        0x12 => panic!("HVC instruction execution, when HVC is not disabled\n======== error stack ======== \n{}",context),
        0x13 => panic!("SMC instruction execution, when SMC is not disabled\n======== error stack ======== \n{}",context),
        0x15 => panic!("SVC call from AArch64 state\n======== error stack ======== \n{}",context),
        0x16 => panic!("HVC instruction execution, when HVC is not disabled\n======== error stack ======== \n{}",context),
        0x17 => panic!("SMC instruction execution, when SMC is not disabled\n======== error stack ======== \n{}",context),
        0x18 => panic!("MSR, MRS, or System instruction execution, that is not reported using EC 0x00, 0x01, or 0x07\n======== error stack ======== \n{}",context),
        0x20 => panic!("Instruction Abort from a lower Exception level\n======== error stack ======== \n{}",context),
        0x21 => panic!("Instruction Abort taken without a change in Exception level\n======== error stack ======== \n{}",context),
        0x22 => panic!("Misaligned PC exception\n======== error stack ======== \n{}",context),
        0x24 => panic!(" Data Abort from a lower Exception levelh\n======== error stack ======== \n{}",context),
        0x25 => panic!("Data Abort taken without a change in Exception level\n======== error stack ======== \n{}",context),
        0x26 => panic!("Stack Pointer Alignment exception\n======== error stack ======== \n{}",context),
        0x28 => panic!("Floating-point exception, if supported\n======== error stack ======== \n{}",context),
        0x2C => panic!("Floating-point exception, if supported\n======== error stack ======== \n{}",context),
        0x2F => panic!("SError interrupt\n======== error stack ======== \n{}",context),
        0x30 => panic!("Breakpoint exception from a lower Exception level\n======== error stack ======== \n{}",context),
        0x31 => panic!("Breakpoint exception taken without a change in Exception level\n======== error stack ======== \n{}",context),
        0x32 => panic!("Software Step exception from a lower Exception level\n======== error stack ======== \n{}",context),
        0x33 => panic!("Software Step exception taken without a change in Exception level\n======== error stack ======== \n{}",context),
        0x34 => panic!("Watchpoint exception from a lower Exception level\n======== error stack ======== \n{}",context),
        0x35 => panic!("Watchpoint exception taken without a change in Exception level\n======== error stack ======== \n{}",context),
        0x38 => panic!("BKPT instruction execution\n======== error stack ======== \n{}",context),
        0x3A => panic!("Vector catch exception from AArch32 state\n======== error stack ======== \n{}",context),
        0x3C => panic!("BRK instruction execution\n======== error stack ======== \n{}",context),
        _ => panic!("Unknown exception class {}\n======== error stack ======== \n{}", ec, context),
    }
}
