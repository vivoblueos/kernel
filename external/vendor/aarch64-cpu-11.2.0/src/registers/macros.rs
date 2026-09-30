// SPDX-License-Identifier: Apache-2.0 OR MIT
//
// Copyright (c) 2018-2023 by the author(s)
//
// Author(s):
//   - Andre Richter <andre.o.richter@gmail.com>

macro_rules! __read_raw {
    ($width:ty, $asm_instr:tt, $asm_reg_name:tt, $asm_width:tt) => {
        /// Reads the raw bits of the CPU register.
        #[inline]
        fn get(&self) -> $width {
            match () {
                #[cfg(target_arch = "aarch64")]
                () => {
                    let reg;
                    unsafe {
                        core::arch::asm!(concat!($asm_instr, " {reg:", $asm_width, "}, ", $asm_reg_name), reg = out(reg) reg, options(nomem, nostack));
                    }
                    reg
                }

                #[cfg(not(target_arch = "aarch64"))]
                () => unimplemented!(),
            }
        }
    };
}

macro_rules! __write_raw {
    ($width:ty, $asm_instr:tt, $asm_reg_name:tt, $asm_width:tt) => {
        /// Writes raw bits to the CPU register.
        #[cfg_attr(not(target_arch = "aarch64"), allow(unused_variables))]
        #[inline]
        fn set(&self, value: $width) {
            match () {
                #[cfg(target_arch = "aarch64")]
                () => {
                    unsafe {
                        core::arch::asm!(concat!($asm_instr, " ", $asm_reg_name, ", {reg:", $asm_width, "}"), reg = in(reg) value, options(nomem, nostack))
                    }
                }

                #[cfg(not(target_arch = "aarch64"))]
                () => unimplemented!(),
            }
        }
    };
}

/// Raw read from system coprocessor registers.
macro_rules! sys_coproc_read_raw {
    ($width:ty, $asm_reg_name:tt, $asm_width:tt) => {
        __read_raw!($width, "mrs", $asm_reg_name, $asm_width);
    };
}

/// Raw write to system coprocessor registers.
macro_rules! sys_coproc_write_raw {
    ($width:ty, $asm_reg_name:tt, $asm_width:tt) => {
        __write_raw!($width, "msr", $asm_reg_name, $asm_width);
    };
}

/// Raw read from (ordinary) registers.
macro_rules! read_raw {
    ($width:ty, $asm_reg_name:tt, $asm_width:tt) => {
        __read_raw!($width, "mov", $asm_reg_name, $asm_width);
    };
}
/// Raw write to (ordinary) registers.
macro_rules! write_raw {
    ($width:ty, $asm_reg_name:tt, $asm_width:tt) => {
        __write_raw!($width, "mov", $asm_reg_name, $asm_width);
    };
}
