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

use super::{irq, registers::esr_el1::ESR_EL1, Context, NR_SWITCH};
use crate::{
    arch::aarch64::{disable_local_irq, enable_local_irq},
    scheduler::{self, ContextSwitchHookHolder},
    support::sideeffect,
    syscalls::{dispatch_syscall, Context as ScContext},
};
use core::{
    arch::{asm, naked_asm},
    mem::offset_of,
    sync::atomic::{compiler_fence, fence, Ordering},
};
use tock_registers::interfaces::Readable;

macro_rules! exception_handler {
    ($name:ident, $cont:path) => {
        #[no_mangle]
        #[naked]
        unsafe extern "C" fn $name() -> ! {
            naked_asm!(
                concat!(
                    "
                    msr DAIFSet, #0x3
                    ",
                    crate::aarch64_save_context_prologue!(),
                    crate::aarch64_save_context!(),
                    "
                    mov x0, sp
                    bl {cont}
                    mov sp, x0
                    ",
                    crate::aarch64_restore_context!(),
                    crate::aarch64_restore_context_epilogue!(),
                    "
                    eret
                    ",
                ),
                lr = const offset_of!(self::Context, lr),
                stack_size = const core::mem::size_of::<self::Context>(),
                x0 = const offset_of!(Context, x0),
                x2 = const offset_of!(Context, x2),
                x4 = const offset_of!(Context, x4),
                x6 = const offset_of!(Context, x6),
                x8 = const offset_of!(Context, x8),
                x10 = const offset_of!(Context, x10),
                x12 = const offset_of!(Context, x12),
                x14 = const offset_of!(Context, x14),
                x16 = const offset_of!(Context, x16),
                x18 = const offset_of!(Context, x18),
                x20 = const offset_of!(Context, x20),
                x22 = const offset_of!(Context, x22),
                x24 = const offset_of!(Context, x24),
                x26 = const offset_of!(Context, x26),
                x28 = const offset_of!(Context, x28),
                spsr = const offset_of!(Context, spsr),
                elr = const offset_of!(Context, elr),
                cont = sym $cont,
            );
        }
    };
}

exception_handler!(el1_fiq, trap_fiq);

exception_handler!(el1_sync, trap_sync);

exception_handler!(el1_irq, trap_irq);

exception_handler!(el1_error, trap_exception);

macro_rules! unsupported_handler {
    ($name:ident, $msg:expr) => {
        #[no_mangle]
        unsafe extern "C" fn $name() {
            panic!($msg);
            asm!("b .");
        }
    };
}

unsupported_handler!(el0_not_supported, "el0 is not supported.");

unsupported_handler!(lowerel_not_supported, "lowerel is not supported.");

#[naked]
unsafe extern "C" fn trap_sync() -> ! {
    naked_asm!(
        "
        mov x19, lr
        mov x20, x0
        bl {handle_svc}
        mov sp, x0
        mov x1, x20
        mov lr, x19
        b {might_switch}
        ",
        handle_svc = sym handle_svc,
        might_switch = sym might_switch,
    );
}

extern "C" fn might_switch(to: &Context, from: &Context) -> usize {
    let to_ptr = to as *const _;
    let from_ptr = from as *const _;
    assert_eq!(to_ptr != from_ptr, from.x8 == NR_SWITCH);
    if to_ptr == from_ptr {
        return from_ptr as usize;
    }
    let saved_sp_ptr: *mut usize = unsafe { from.x0 as *mut usize };
    if !saved_sp_ptr.is_null() {
        unsafe {
            sideeffect();
            saved_sp_ptr.write_volatile(from_ptr as usize)
        };
    }
    let hook: *mut ContextSwitchHookHolder =
        unsafe { from.x2 as *mut scheduler::ContextSwitchHookHolder<'_> };
    if !hook.is_null() {
        sideeffect();
        unsafe {
            scheduler::save_context_finish_hook(Some(&mut *hook));
        }
    }
    to as *const _ as usize
}

extern "C" fn handle_svc(context: &mut Context) -> usize {
    let esr = ESR_EL1.get();
    let ec = (esr >> 26) & 0x3F;
    let old_sp = context as *const _ as usize;
    if ec != 0x15 {
        show_exception(ec, context);
        return old_sp;
    }
    if context.x8 == NR_SWITCH {
        return context.x1;
    }
    compiler_fence(Ordering::SeqCst);
    let sc = ScContext {
        nr: context.x8,
        args: [
            context.x0, context.x1, context.x2, context.x3, context.x4, context.x5,
        ],
    };
    enable_local_irq();
    context.x0 = dispatch_syscall(&sc);
    disable_local_irq();
    compiler_fence(Ordering::SeqCst);
    old_sp
}

extern "C" fn trap_exception(context: &mut Context) -> usize {
    let sp = context as *const _ as usize;
    let esr = ESR_EL1.get();
    let ec = (esr >> 26) & 0x3F;
    show_exception(ec, context);
    sp
}

extern "C" fn trap_irq(context: &mut Context) -> usize {
    let sp = context as *const _ as usize;
    let irq = irq::get_interrupt();
    irq::trigger_irq(irq);
    irq::end_interrupt(irq);
    sp
}

extern "C" fn trap_fiq(context: &mut Context) -> usize {
    let sp = context as *const _ as usize;
    let fiq = irq::get_interrupt();
    if u32::from(fiq) != 1023 {
        irq::trigger_irq(fiq);
    }
    irq::end_interrupt(fiq);
    sp
}

fn show_exception(ec: u64, context: &mut Context) {
    match ec {
        0x00 => panic!("Unknow reason Exceptions\n======== error stack ======== \n{}",context),
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
        _ => todo!(),
    }
}
