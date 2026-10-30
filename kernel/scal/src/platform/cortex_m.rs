// The below Copyright and License apply uniformly to all files in this
// repository, unless a different copyright/license is mentioned
// explicitly.
//
// Copyright (c) 2020-2021, Jason White
// Copyright (c) 2018-2019, Trustees of Indiana University
//     ("University Works" via Baojun Wang)
// Copyright (c) 2018-2019, Ryan Newton
//     ("Traditional Works of Scholarship")
//
// All rights reserved.
//
// BSD 2-Clause License
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//
// * Redistributions of source code must retain the above copyright notice, this
//   list of conditions and the following disclaimer.
//
// * Redistributions in binary form must reproduce the above copyright notice,
//   this list of conditions and the following disclaimer in the documentation
//   and/or other materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
// FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
// DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
// SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
// CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
// OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

use core::arch::asm;

#[inline(always)]
pub unsafe fn syscall0(n: usize) -> usize {
    let mut ret: usize;
    asm!(
        "movs {temp}, r7",
        "movs r7, {n}",
        "svc 0",
        "movs r7, {temp}",
        n = in(reg) n,
        temp = out(reg) _,
        lateout("r0") ret,
        options(nostack)
    );
    ret
}

#[inline(always)]
pub unsafe fn syscall1(n: usize, arg1: usize) -> usize {
    let mut ret: usize;
    asm!(
        "movs {temp}, r7",
        "movs r7, {n}",
        "svc 0",
        "movs r7, {temp}",
        n = in(reg) n,
        temp = out(reg) _,
        inlateout("r0") arg1 => ret,
        options(nostack)
    );
    ret
}

#[inline(always)]
pub unsafe fn syscall2(n: usize, arg1: usize, arg2: usize) -> usize {
    let mut ret: usize;
    asm!(
        "movs {temp}, r7",
        "movs r7, {n}",
        "svc 0",
        "movs r7, {temp}",
        n = in(reg) n,
        temp = out(reg) _,
        inlateout("r0") arg1 => ret,
        in("r1") arg2,
        options(nostack)
    );
    ret
}

#[inline(always)]
pub unsafe fn syscall3(n: usize, arg1: usize, arg2: usize, arg3: usize) -> usize {
    let mut ret: usize;
    asm!(
        "movs {temp}, r7",
        "movs r7, {n}",
        "svc 0",
        "movs r7, {temp}",
        n = in(reg) n,
        temp = out(reg) _,
        inlateout("r0") arg1 => ret,
        in("r1") arg2,
        in("r2") arg3,
        options(nostack)
    );
    ret
}

#[inline(always)]
pub unsafe fn syscall4(n: usize, arg1: usize, arg2: usize, arg3: usize, arg4: usize) -> usize {
    let mut ret: usize;
    asm!(
        "movs {temp}, r7",
        "movs r7, {n}",
        "svc 0",
        "movs r7, {temp}",
        n = in(reg) n,
        temp = out(reg) _,
        inlateout("r0") arg1 => ret,
        in("r1") arg2,
        in("r2") arg3,
        in("r3") arg4,
        options(nostack)
    );
    ret
}

#[inline(always)]
pub unsafe fn syscall5(
    n: usize,
    arg1: usize,
    arg2: usize,
    arg3: usize,
    arg4: usize,
    arg5: usize,
) -> usize {
    let mut ret: usize;
    asm!(
        "movs {temp}, r7",
        "movs r7, {n}",
        "svc 0",
        "movs r7, {temp}",
        n = in(reg) n,
        temp = out(reg) _,
        inlateout("r0") arg1 => ret,
        in("r1") arg2,
        in("r2") arg3,
        in("r3") arg4,
        in("r4") arg5,
        options(nostack)
    );
    ret
}

#[inline(always)]
pub unsafe fn syscall6(
    n: usize,
    arg1: usize,
    arg2: usize,
    arg3: usize,
    arg4: usize,
    arg5: usize,
    arg6: usize,
) -> usize {
    let mut ret: usize;

    // NOTE: On ARMv4t, `movs` must be used instead of `mov`.
    asm!(
        "movs {temp}, r7",
        "movs r7, {n}",
        "svc 0",
        "movs r7, {temp}",
        n = in(reg) n,
        temp = out(reg) _,
        inlateout("r0") arg1 => ret,
        in("r1") arg2,
        in("r2") arg3,
        in("r3") arg4,
        in("r4") arg5,
        in("r5") arg6,
        options(nostack)
    );
    ret
}
