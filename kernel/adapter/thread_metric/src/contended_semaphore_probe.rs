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

#![no_std]
#![no_main]

extern crate librs;
extern crate rsrt;

use blueos::{scheduler::InsertToEnd, sync::Semaphore, thread, time::Tick};
use core::sync::atomic::{AtomicBool, Ordering};

static PING: Semaphore = Semaphore::new();
static PONG: Semaphore = Semaphore::new();
static STOP: AtomicBool = AtomicBool::new(false);

#[unsafe(no_mangle)]
pub extern "C" fn main() -> i32 {
    librs::stdio::init();
    librs::pthread::register_my_posix_tcb();

    assert!(PING.init(1));
    assert!(PONG.init(0));

    thread::spawn(|| loop {
        assert!(PONG.acquire_notimeout::<InsertToEnd>());
        if STOP.load(Ordering::Relaxed) {
            break;
        }
        PING.release();
    })
    .unwrap();

    for _ in 0..6 {
        let end = Tick::after(Tick::from_millis(2000));
        let mut count = 0u32;
        while Tick::now().0 < end.0 {
            assert!(PING.acquire_notimeout::<InsertToEnd>());
            PONG.release();
            count += 1;
        }
        unsafe {
            libc::printf(c"Time Period Total: %u\n".as_ptr(), count);
        }
    }
    STOP.store(true, Ordering::Relaxed);
    PONG.release();

    loop {
        core::hint::spin_loop();
    }
}
