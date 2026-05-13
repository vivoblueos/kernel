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

//! Register capture for RISC-V coredump.
//!
//! Register order follows Linux riscv_user_regs_struct:
//!   pc, ra, sp, gp, tp, t0..t6, fp, a0..a7, s1..s11, (s0=fp)
//! Total: 32 registers × usize width.

use crate::arch;

/// RISC-V has 32 general-purpose registers in the Linux user_regs_struct order.
const REGS: usize = 32;

/// Register dump size: 32 × usize (4 bytes on riscv32, 8 bytes on riscv64).
const REGSET_SZ: usize = REGS * core::mem::size_of::<usize>();

#[inline(never)]
pub(crate) fn capture_regs(ctx: &arch::Context) -> [u8; REGSET_SZ] {
    let mut buf = [0u8; REGSET_SZ];

    // Linux RISCV user_regs_struct order:
    //   [0] pc, [1] ra, [2] sp, [3] gp, [4] tp
    //   [5-7] t0-t2, [8] fp(s0), [9-16] a0-a7
    //   [17-19] t3-t5, [20] t6, [21-31] s1-s11
    let sp = ctx as *const arch::Context as usize;

    let regs: [usize; REGS] = [
        ctx.mepc, // pc
        ctx.ra,   // ra
        sp,       // sp
        ctx.gp,   // gp
        ctx.tp,   // tp
        ctx.t0,   // t0
        ctx.t1,   // t1
        ctx.t2,   // t2
        ctx.fp,   // fp (s0)
        ctx.a0,
        ctx.a1,
        ctx.a2,
        ctx.a3,
        ctx.a4,
        ctx.a5,
        ctx.a6,
        ctx.a7,
        ctx.t3,
        ctx.t4,
        ctx.t5,
        ctx.t6,
        ctx.s1,
        ctx.s2,
        ctx.s3,
        ctx.s4,
        ctx.s5,
        ctx.s6,
        ctx.s7,
        ctx.s8,
        ctx.s9,
        ctx.s10,
        ctx.s11,
    ];
    for (i, &r) in regs.iter().enumerate() {
        let off = i * core::mem::size_of::<usize>();
        buf[off..off + core::mem::size_of::<usize>()].copy_from_slice(&r.to_ne_bytes());
    }
    buf
}

#[inline(never)]
pub fn capture_current_regs() -> [u8; REGSET_SZ] {
    let thread = crate::scheduler::current_thread_ref();
    let sp = thread.saved_sp();
    if sp != 0 {
        if let Some(ctx) = unsafe { (sp as *const arch::Context).as_ref() } {
            return capture_regs(ctx);
        }
    }
    [0u8; REGSET_SZ]
}
