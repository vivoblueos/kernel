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

//! Register capture for AArch64 coredump.
//!
//! Register order follows Linux AArch64 user_regs_struct:
//!   x0..x30, sp, pc, pstate  (34 × 8 = 272 bytes)

use crate::arch;

/// Register count matching Linux AArch64 user_regs_struct.
const REGS: usize = 34;

#[inline(never)]
pub fn capture_regs(ctx: &arch::Context) -> [u8; REGS * 8] {
    let mut buf = [0u8; REGS * 8];

    // x0..x28
    let gpr: [usize; 29] = [
        ctx.x0, ctx.x1, ctx.x2, ctx.x3, ctx.x4, ctx.x5, ctx.x6, ctx.x7, ctx.x8, ctx.x9, ctx.x10,
        ctx.x11, ctx.x12, ctx.x13, ctx.x14, ctx.x15, ctx.x16, ctx.x17, ctx.x18, ctx.x19, ctx.x20,
        ctx.x21, ctx.x22, ctx.x23, ctx.x24, ctx.x25, ctx.x26, ctx.x27, ctx.x28,
    ];
    for (i, &r) in gpr.iter().enumerate() {
        buf[i * 8..(i + 1) * 8].copy_from_slice(&r.to_ne_bytes());
    }

    // x29 = fp, x30 = lr
    buf[29 * 8..30 * 8].copy_from_slice(&ctx.fp.to_ne_bytes());
    buf[30 * 8..31 * 8].copy_from_slice(&ctx.lr.to_ne_bytes());

    // SP = ctx pointer base address
    let sp = ctx as *const arch::Context as usize;
    buf[31 * 8..32 * 8].copy_from_slice(&sp.to_ne_bytes());

    // PC = ctx.elr
    buf[32 * 8..33 * 8].copy_from_slice(&ctx.elr.to_ne_bytes());

    // PSTATE = ctx.spsr
    buf[33 * 8..34 * 8].copy_from_slice(&ctx.spsr.to_ne_bytes());

    buf
}

#[inline(never)]
pub fn capture_current_regs() -> [u8; REGS * 8] {
    let thread = crate::scheduler::current_thread_ref();
    let sp = thread.saved_sp();
    if sp != 0 {
        if let Some(ctx) = unsafe { (sp as *const arch::Context).as_ref() } {
            return capture_regs(ctx);
        }
    }
    [0u8; REGS * 8]
}
