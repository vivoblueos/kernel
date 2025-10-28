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

pub struct EsrEl1;

impl Readable for EsrEl1 {
    type T = u64;
    type R = ();

    #[inline]
    fn get(&self) -> Self::T {
        let esr;
        unsafe {
            core::arch::asm!(
                "mrs {}, esr_el1",
                out(reg) esr,
                options(nomem, nostack, preserves_flags)
            );
        }
        esr
    }
}

pub const ESR_EL1: EsrEl1 = EsrEl1 {};
