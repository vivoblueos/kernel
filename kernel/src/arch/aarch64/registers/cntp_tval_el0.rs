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

use tock_registers::interfaces::{Readable, Writeable};

pub struct CntpTvalEl0;

impl Readable for CntpTvalEl0 {
    type T = u64;
    type R = ();

    #[inline]
    fn get(&self) -> Self::T {
        let value;
        unsafe {
            core::arch::asm!(
                "mrs {}, cntp_tval_el0",
                out(reg) value,
                options(nomem, nostack)
            );
        }
        value
    }
}

impl Writeable for CntpTvalEl0 {
    type T = u64;
    type R = ();

    #[inline]
    fn set(&self, value: Self::T) {
        unsafe {
            core::arch::asm!(
                "msr cntp_tval_el0, {}",
                in(reg) value,
                options(nomem, nostack)
            );
        }
    }
}

pub const CNTP_TVAL_EL0: CntpTvalEl0 = CntpTvalEl0 {};
