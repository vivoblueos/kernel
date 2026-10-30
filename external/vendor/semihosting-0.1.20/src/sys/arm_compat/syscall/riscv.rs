// SPDX-License-Identifier: Apache-2.0 OR MIT

use core::arch::asm;

use super::{OperationNumber, ParamRegR, ParamRegW, RetReg};

/// Raw semihosting call with a parameter that will be read + modified by the host
#[inline]
pub unsafe fn syscall(number: OperationNumber, parameter: ParamRegW<'_>) -> RetReg {
    unsafe {
        let r;
        asm!(
            ".balign 16",
            ".option push",
            ".option norvc",
            "slli zero, zero, 0x1F",
            "ebreak",
            "srai zero, zero, 0x7",
            ".option pop",
            inout("a0") number.0 as usize => r, // OPERATION NUMBER REGISTER => RETURN REGISTER
            // Use inout because operation such as SYS_ELAPSED suggest that
            // PARAMETER REGISTER may be changed.
            inout("a1") parameter.0 => _, // PARAMETER REGISTER
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
            ".balign 16",
            ".option push",
            ".option norvc",
            "slli zero, zero, 0x1F",
            "ebreak",
            "srai zero, zero, 0x7",
            ".option pop",
            inout("a0") number.0 as usize => r, // OPERATION NUMBER REGISTER => RETURN REGISTER
            // Use inout because operation such as SYS_ELAPSED suggest that
            // PARAMETER REGISTER may be changed.
            inout("a1") parameter.0 => _, // PARAMETER REGISTER
            options(nostack, preserves_flags, readonly),
        );
        RetReg(r)
    }
}
