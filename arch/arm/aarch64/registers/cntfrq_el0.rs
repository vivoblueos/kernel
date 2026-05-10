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

use tock_registers::interfaces::Readable;

pub struct CntfrqEl0;

impl Readable for CntfrqEl0 {
    type T = u64;
    type R = ();

    #[inline]
    fn get(&self) -> Self::T {
        let value;
        unsafe {
            core::arch::asm!(
                "mrs {}, cntfrq_el0",
                out(reg) value,
                options(nomem, nostack)
            );
        }
        value
    }
}

pub const CNTFRQ_EL0: CntfrqEl0 = CntfrqEl0 {};
