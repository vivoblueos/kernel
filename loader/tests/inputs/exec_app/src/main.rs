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

// ESP32C3 UART0 MMIO registers (APB bus, base 0x6000_0000).
const UART0_BASE: usize = 0x6000_0000;
const UART_FIFO_OFFSET: usize = 0x00;
const UART_STATUS_OFFSET: usize = 0x1C;
const UART_FSM_STATUS_OFFSET: usize = 0x6C;

fn uart_putc(c: u8) {
    let fifo = (UART0_BASE + UART_FIFO_OFFSET) as *mut u32;
    let status = (UART0_BASE + UART_STATUS_OFFSET) as *const u32;
    // Wait until TX FIFO has room (< 128 bytes).
    while (unsafe { status.read_volatile() } >> 16) & 0x3FF >= 128 {
        core::hint::spin_loop();
    }
    unsafe {
        fifo.write_volatile(c as u32);
    }
}

fn uart_puts(s: &str) {
    for byte in s.bytes() {
        if byte == b'\n' {
            uart_putc(b'\r');
        }
        uart_putc(byte);
    }
    // Drain TX FIFO + wait for transmitter idle.
    let status = (UART0_BASE + UART_STATUS_OFFSET) as *const u32;
    let fsm_status = (UART0_BASE + UART_FSM_STATUS_OFFSET) as *const u32;
    while (unsafe { status.read_volatile() } >> 16) & 0x3FF != 0 {
        core::hint::spin_loop();
    }
    while (unsafe { fsm_status.read_volatile() } >> 4) & 0xF != 0 {
        core::hint::spin_loop();
    }
}

#[no_mangle]
pub extern "C" fn _start() -> u32 {
    uart_puts("hello from esp32c3\n");

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
