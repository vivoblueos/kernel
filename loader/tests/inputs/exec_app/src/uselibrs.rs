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

use core::alloc::{GlobalAlloc, Layout};

// librs links liballoc even though this test does not allocate.
struct UnusedAllocator;

unsafe impl GlobalAlloc for UnusedAllocator {
    unsafe fn alloc(&self, _layout: Layout) -> *mut u8 {
        core::ptr::null_mut()
    }

    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout) {}
}

#[global_allocator]
static ALLOCATOR: UnusedAllocator = UnusedAllocator;

// RV32IMC has no A extension. libatomic uses these hooks for its fallback.
#[no_mangle]
pub extern "C" fn disable_local_irq_save() -> usize {
    let old: usize;
    unsafe {
        core::arch::asm!(
            "csrrci {old}, mstatus, 8",
            old = out(reg) old,
            options(nostack),
        );
    }
    old
}

#[no_mangle]
pub extern "C" fn enable_local_irq_restore(old: usize) {
    unsafe {
        core::arch::asm!("csrw mstatus, {old}", old = in(reg) old, options(nostack));
    }
}

#[no_mangle]
pub extern "C" fn _start() -> i32 {
    librs::time::msleep(1)
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    loop {
        core::hint::spin_loop();
    }
}
