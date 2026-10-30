// SPDX-License-Identifier: Apache-2.0 OR MIT

use core::arch::asm;

use super::{OperationCode, ParamRegR, ParamRegW, RetReg};

/// syscall with 0 arguments
#[inline]
pub unsafe fn syscall0(op: OperationCode) -> (RetReg, RetReg) {
    unsafe {
        let r1;
        let r2;
        asm!(
            "sdbbp 1",
            inout("$2") 1_usize => r1,
            out("$3") r2,
            out("$4") _,
            out("$5") _,
            in("$25") op.0,
            options(nostack, readonly),
        );
        (RetReg(r1), RetReg(r2))
    }
}

/// Raw semihosting call with 1 parameter that will be read + modified by the host
#[inline]
pub unsafe fn syscall1(op: OperationCode, arg1: ParamRegW<'_>) -> (RetReg, RetReg) {
    unsafe {
        let r1;
        let r2;
        asm!(
            "sdbbp 1",
            inout("$2") 1_usize => r1,
            out("$3") r2,
            inout("$4") arg1.0 => _,
            out("$5") _,
            in("$25") op.0,
            options(nostack),
        );
        (RetReg(r1), RetReg(r2))
    }
}

/// Raw semihosting call with 1 parameter that will be read (but not modified) by the host
#[inline]
pub unsafe fn syscall1_readonly(op: OperationCode, arg1: ParamRegR<'_>) -> (RetReg, RetReg) {
    unsafe {
        let r1;
        let r2;
        asm!(
            "sdbbp 1",
            inout("$2") 1_usize => r1,
            out("$3") r2,
            inout("$4") arg1.0 => _,
            out("$5") _,
            in("$25") op.0,
            options(nostack, readonly),
        );
        (RetReg(r1), RetReg(r2))
    }
}

/// Raw semihosting call with 2 parameters that will be read + modified by the host
#[inline]
pub unsafe fn syscall2(
    op: OperationCode,
    arg1: ParamRegW<'_>,
    arg2: ParamRegW<'_>,
) -> (RetReg, RetReg) {
    unsafe {
        let r1;
        let r2;
        asm!(
            "sdbbp 1",
            inout("$2") 1_usize => r1,
            out("$3") r2,
            inout("$4") arg1.0 => _,
            inout("$5") arg2.0 => _,
            in("$25") op.0,
            options(nostack),
        );
        (RetReg(r1), RetReg(r2))
    }
}

/// Raw semihosting call with 2 parameters that will be read (but not modified) by the host
#[inline]
pub unsafe fn syscall2_readonly(
    op: OperationCode,
    arg1: ParamRegR<'_>,
    arg2: ParamRegR<'_>,
) -> (RetReg, RetReg) {
    unsafe {
        let r1;
        let r2;
        asm!(
            "sdbbp 1",
            inout("$2") 1_usize => r1,
            out("$3") r2,
            inout("$4") arg1.0 => _,
            inout("$5") arg2.0 => _,
            in("$25") op.0,
            options(nostack, readonly),
        );
        (RetReg(r1), RetReg(r2))
    }
}

/// Raw semihosting call with 3 parameters that will be read + modified by the host
#[inline]
pub unsafe fn syscall3(
    op: OperationCode,
    arg1: ParamRegW<'_>,
    arg2: ParamRegW<'_>,
    arg3: ParamRegW<'_>,
) -> (RetReg, RetReg) {
    unsafe {
        let r1;
        let r2;
        asm!(
            "sdbbp 1",
            inout("$2") 1_usize => r1,
            out("$3") r2,
            inout("$4") arg1.0 => _,
            inout("$5") arg2.0 => _,
            in("$6") arg3.0,
            in("$25") op.0,
            options(nostack),
        );
        (RetReg(r1), RetReg(r2))
    }
}

/// Raw semihosting call with 3 parameters that will be read (but not modified) by the host
#[inline]
pub unsafe fn syscall3_readonly(
    op: OperationCode,
    arg1: ParamRegR<'_>,
    arg2: ParamRegR<'_>,
    arg3: ParamRegR<'_>,
) -> (RetReg, RetReg) {
    unsafe {
        let r1;
        let r2;
        asm!(
            "sdbbp 1",
            inout("$2") 1_usize => r1,
            out("$3") r2,
            inout("$4") arg1.0 => _,
            inout("$5") arg2.0 => _,
            in("$6") arg3.0,
            in("$25") op.0,
            options(nostack, readonly),
        );
        (RetReg(r1), RetReg(r2))
    }
}

/// Raw semihosting call with 4 parameters that will be read + modified by the host
#[inline]
pub unsafe fn syscall4(
    op: OperationCode,
    arg1: ParamRegW<'_>,
    arg2: ParamRegW<'_>,
    arg3: ParamRegW<'_>,
    arg4: ParamRegW<'_>,
) -> (RetReg, RetReg) {
    unsafe {
        let r1;
        let r2;
        asm!(
            "sdbbp 1",
            inout("$2") 1_usize => r1,
            out("$3") r2,
            inout("$4") arg1.0 => _,
            inout("$5") arg2.0 => _,
            in("$6") arg3.0,
            in("$7") arg4.0,
            in("$25") op.0,
            options(nostack),
        );
        (RetReg(r1), RetReg(r2))
    }
}

/// Raw semihosting call with 4 parameters that will be read (but not modified) by the host
#[inline]
pub unsafe fn syscall4_readonly(
    op: OperationCode,
    arg1: ParamRegR<'_>,
    arg2: ParamRegR<'_>,
    arg3: ParamRegR<'_>,
    arg4: ParamRegR<'_>,
) -> (RetReg, RetReg) {
    unsafe {
        let r1;
        let r2;
        asm!(
            "sdbbp 1",
            inout("$2") 1_usize => r1,
            out("$3") r2,
            inout("$4") arg1.0 => _,
            inout("$5") arg2.0 => _,
            in("$6") arg3.0,
            in("$7") arg4.0,
            in("$25") op.0,
            options(nostack, readonly),
        );
        (RetReg(r1), RetReg(r2))
    }
}
