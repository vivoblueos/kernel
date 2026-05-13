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

//! Register capture for ARM Cortex-M coredump.
//!
//! Register order follows Linux ARM user_regs_struct:
//!   r0..r15, cpsr, orig_r0  (18 × 4 = 72 bytes)

use crate::arch;

/// Register count matching Linux ARM user_regs_struct.
const REGS: usize = 18;

#[inline(never)]
pub fn capture_regs(ctx: &arch::Context) -> [u8; REGS * 4] {
    let mut buf = [0u8; REGS * 4];

    // On Cortex-M, saved_sp points to where r4 was stored (callee-saved block).
    // The hardware auto-saves r0-r3,r12,lr,pc,xpsr below that.
    // Calculate PSP = saved_sp + 4*8 (r4-r11) + 4*8 (r0-r3,r12,lr,pc,xpsr).
    let psp = ctx as *const arch::Context as usize + 64;

    let regs: [u32; REGS] = [
        ctx.r0 as u32,
        ctx.r1 as u32,
        ctx.r2 as u32,
        ctx.r3 as u32,
        ctx.r4 as u32,
        ctx.r5 as u32,
        ctx.r6 as u32,
        ctx.r7 as u32,
        ctx.r8 as u32,
        ctx.r9 as u32,
        ctx.r10 as u32,
        ctx.r11 as u32,
        ctx.r12 as u32,
        psp as u32,              // SP = R13
        ctx.lr as u32,           // LR = R14
        ctx.pc as u32,           // PC = R15
        ctx.xpsr as u32,         // CPSR
        0,                       // orig_r0
    ];
    for (i, &r) in regs.iter().enumerate() {
        buf[i * 4..(i + 1) * 4].copy_from_slice(&r.to_ne_bytes());
    }
    buf
}

#[inline(never)]
pub fn capture_current_regs() -> [u8; REGS * 4] {
    let thread = crate::scheduler::current_thread_ref();
    let sp = thread.saved_sp();
    if sp != 0 {
        if let Some(ctx) = unsafe { (sp as *const arch::Context).as_ref() } {
            return capture_regs(ctx);
        }
    }
    [0u8; REGS * 4]
}
