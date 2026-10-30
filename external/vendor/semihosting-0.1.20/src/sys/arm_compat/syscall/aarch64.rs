// SPDX-License-Identifier: Apache-2.0 OR MIT

use core::arch::asm;

use super::{OperationNumber, ParamRegR, ParamRegW, RetReg};

/// Raw semihosting call with a parameter that will be read + modified by the host
#[inline]
pub unsafe fn syscall(number: OperationNumber, parameter: ParamRegW<'_>) -> RetReg {
    unsafe {
        let r;
        asm!(
            "hlt 0xF000",
            in("w0") number.0, // OPERATION NUMBER REGISTER
            // Use inout because operation such as SYS_ELAPSED suggest that
            // the PARAMETER REGISTER may be changed.
            inout("x1") parameter.0 => _, // PARAMETER REGISTER
            lateout("x0") r, // RETURN REGISTER
            options(nostack, preserves_flags),
        );
        RetReg(r)
    }
}

/// Raw semihosting call with a parameter that will be read (but not modified) by the host
#[inline]
pub unsafe fn syscall_readonly(number: OperationNumber, parameter: ParamRegR<'_>) -> RetReg {
    unsafe {
        let r;
        asm!(
            "hlt 0xF000",
            in("w0") number.0, // OPERATION NUMBER REGISTER
            // Use inout because operation such as SYS_ELAPSED suggest that
            // the PARAMETER REGISTER may be changed.
            inout("x1") parameter.0 => _, // PARAMETER REGISTER
            lateout("x0") r, // RETURN REGISTER
            options(nostack, preserves_flags, readonly),
        );
        RetReg(r)
    }
}
