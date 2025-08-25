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

//! Program Status Register

use core::arch::asm;

/// Program Status Register
#[derive(Clone, Copy, Debug, Default)]
pub struct Xpsr {
    bits: u32,
}

impl Xpsr {
    #[inline]
    pub fn from_bits(bits: u32) -> Self {
        Self { bits }
    }

    /// Returns the contents of the register as raw bits
    #[inline]
    pub fn bits(self) -> u32 {
        self.bits
    }

    /// Exception number bits [8:0]
    #[inline]
    pub fn e(self) -> u32 {
        self.bits & 0xFF
    }

    /// IT/ICI/ECI Value
    #[inline]
    pub fn it_val(self) -> u32 {
        (self.bits >> 10) & 0x3F
    }

    /// Greater-than or equal flag, bits [19:16]
    #[inline]
    pub fn ge(self) -> bool {
        (self.bits >> 16) & 0xF != 0
    }

    /// Branch target identification active
    #[inline]
    pub fn b(self) -> bool {
        self.bits & (1 << 21) == (1 << 21)
    }

    /// T32 state
    #[inline]
    pub fn t(self) -> bool {
        self.bits & (1 << 24) == (1 << 24)
    }

    /// IT/ICI/ECI flag
    #[inline]
    pub fn it(self) -> bool {
        // [{EPSR[26:25], EPSR[11:10]} != 0]
        ((self.bits >> 25) & 0x3) << 6 | ((self.bits >> 10) & 0x3) != 0
    }

    /// DSP overflow and saturation flag
    #[inline]
    pub fn q(self) -> bool {
        self.bits & (1 << 27) == (1 << 27)
    }

    /// Overflow flag
    #[inline]
    pub fn v(self) -> bool {
        self.bits & (1 << 28) == (1 << 28)
    }

    /// Carry or borrow flag
    #[inline]
    pub fn c(self) -> bool {
        self.bits & (1 << 29) == (1 << 29)
    }

    /// Zero flag
    #[inline]
    pub fn z(self) -> bool {
        self.bits & (1 << 30) == (1 << 30)
    }

    /// Negative flag
    #[inline]
    pub fn n(self) -> bool {
        self.bits & (1 << 31) == (1 << 31)
    }
}

/// Reads the CPU register
#[inline]
pub fn read() -> Xpsr {
    let bits;
    // SAFETY: Safe register read operation
    unsafe { asm!("mrs {}, XPSR", out(reg) bits, options(nomem, nostack, preserves_flags)) };
    Xpsr { bits }
}

impl core::fmt::Display for Xpsr {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        writeln!(f, "XPSR: 0x{:08x}", self.bits)?;

        // Display Exception Number
        writeln!(f, "  Exception Number: {}", self.e())?;

        // Display T32 state
        if self.t() {
            writeln!(f, "  - T32 instruction set")?;
        } else {
            writeln!(f, "  - Invalid state")?;
        }

        // Display branch target identification state
        if self.b() {
            writeln!(f, "  - Branch target identification inactive")?;
        } else {
            writeln!(f, "  - Branch target identification active")?;
        }

        // Display IT/ICI/ECI state
        writeln!(f, "  IT/ICI/ECI flag: {}", self.it())?;
        writeln!(f, "  IT/ICI/ECI value: {}", self.it_val())?;

        // Display condition flags
        writeln!(f, "  Condition flags:")?;
        writeln!(
            f,
            "    N={} Z={} C={} V={} Q={}",
            self.n() as u8,
            self.z() as u8,
            self.c() as u8,
            self.v() as u8,
            self.q() as u8
        )?;

        Ok(())
    }
}

#[cfg(all(test, not(target_os = "none")))]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn test_xpsr_flags() {
        let mut xpsr = Xpsr { bits: 0 };

        xpsr.bits = 1 << 31;
        assert!(xpsr.n());
        xpsr.bits = 0;
        assert!(!xpsr.n());

        xpsr.bits = 1 << 30;
        assert!(xpsr.z());
        xpsr.bits = 0;
        assert!(!xpsr.z());

        xpsr.bits = 1 << 29;
        assert!(xpsr.c());
        xpsr.bits = 0;
        assert!(!xpsr.c());

        xpsr.bits = 1 << 28;
        assert!(xpsr.v());
        xpsr.bits = 0;
        assert!(!xpsr.v());

        xpsr.bits = 1 << 27;
        assert!(xpsr.q());
        xpsr.bits = 0;
        assert!(!xpsr.q());

        xpsr.bits = 1 << 24;
        assert!(xpsr.t());
        xpsr.bits = 0;
        assert!(!xpsr.t());

        xpsr.bits = 0x1F;
        assert_eq!(xpsr.e(), 0x1F);
        xpsr.bits = 0;
        assert_eq!(xpsr.e(), 0);
    }
}
