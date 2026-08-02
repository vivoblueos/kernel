// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
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

#![no_main]
#![no_std]

use core::ptr::{addr_of, addr_of_mut};

const INITIAL_VALUE: u32 = 0x1357_2468;
const WRITTEN_VALUE: u32 = 0x89ab_cdef;
#[used]
static mut INITIALIZED: u32 = INITIAL_VALUE;

#[used]
static mut ZEROED: u32 = 0;

#[no_mangle]
pub extern "C" fn _start() -> u32 {
    unsafe {
        let initialized = addr_of!(INITIALIZED).read_volatile();
        let zeroed = addr_of!(ZEROED).read_volatile();
        if initialized != INITIAL_VALUE || zeroed != 0 {
            return 0;
        }
        addr_of_mut!(ZEROED).write_volatile(WRITTEN_VALUE);
        initialized ^ addr_of!(ZEROED).read_volatile()
    }
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    loop {
        core::hint::spin_loop();
    }
}
