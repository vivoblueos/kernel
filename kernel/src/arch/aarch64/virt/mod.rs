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

pub mod hyper;
pub mod vector;
pub use hyper::{get_current_el, hyp_init};

// Temporary placeholder
#[no_mangle]
pub extern "C" fn hyper_trap_irq(_context: &mut crate::arch::aarch64::Context) -> usize {
    0
}

#[no_mangle]
pub extern "C" fn hyper_trap_fiq(_context: &mut crate::arch::aarch64::Context) -> usize {
    0
}

pub fn virt_init() {
    hyp_init();
}

// Issue an HVC call to EL2
// func_id: Function ID (x0)
// arg1: Argument 1 (x1)
// arg2: Argument 2 (x2)
pub fn hvc_call(func_id: u64, arg1: u64, arg2: u64) -> u64 {
    let result: u64;
    unsafe {
        core::arch::asm!(
            "hvc #0",
            inout("x0") func_id => result,
            in("x1") arg1,
            in("x2") arg2,
            options(nostack)
        );
    }
    result
}
