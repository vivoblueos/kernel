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

use super::{get_current_vcpu_id, vgic, virtio};
use blueos_hal::isr::IsrDesc;

// PL011 UART addresses for QEMU Virt
const UART0_DR: u32 = 0x0900_0000;

#[inline]
pub fn handle_read(offset: u64) -> u64 {
    match offset {
        0xFE0 => 0x11,
        0xFE4 => 0x10,
        0xFE8 => 0x14,
        0xFEC => 0x00,
        0xFF0 => 0x0D,
        0xFF4 => 0xF0,
        0xFF8 => 0x05,
        0xFFC => 0xB1,
        0x018 => 0x90,
        0x024 => 0x24,
        0x030 => 0x301,
        0x038 => 0x00,
        _ => 0,
    }
}

#[inline]
pub fn handle_write(offset: u64, value: u64) {
    match offset {
        0x000 => {
            let c = (value & 0xFF) as u8;
            let mut writer = crate::console::EarlyConsole {};
            use core::fmt::Write;
            writer
                .write_str(core::str::from_utf8(&[c]).unwrap_or(""))
                .unwrap();
        }
        0x030..=0x044 => (),
        _ => {}
    }
}

pub fn handle_physical_uart_interrupt() {
    unsafe {
        let uart_base = UART0_DR as *mut u32;
        let mut injected = false;

        while (core::ptr::read_volatile(uart_base.add(0x18 / 4)) & (1 << 4)) == 0 {
            let mut byte = core::ptr::read_volatile(uart_base) as u8;
            virtio::VIRTIO_CONSOLE.inject_rx(byte);
            injected = true;
        }

        if injected {
            if let Some(vcpu_id) = get_current_vcpu_id() {
                vgic::inject_irq(vcpu_id, 48);
            }
        }

        core::ptr::write_volatile(uart_base.add(0x44 / 4), (1 << 4) | (1 << 6));
    }
}

// Enable UART RX and RT interrupts in PL011 IMSC register
// Without this, the hardware won't assert IRQ 33 when keys are pressed!
pub fn enable_physical_uart_interrupts() {
    unsafe {
        let uart_base = UART0_DR as *mut u32;
        let imsc = uart_base.add(0x38 / 4);
        core::ptr::write_volatile(imsc, core::ptr::read_volatile(imsc) | (1 << 4) | (1 << 6));
    }
}

pub fn cleanup_physical_uart_interrupts() {
    unsafe {
        let uart_base = UART0_DR as *mut u32;

        // Disable RTI (bit 6) because BlueOS's native driver doesn't handle it.
        // If we leave it enabled, it causes an infinite interrupt storm in EL1!
        let imsc = uart_base.add(0x38 / 4);
        let mut val = core::ptr::read_volatile(imsc);
        val &= !(1 << 6);
        core::ptr::write_volatile(imsc, val);

        // Clear any pending RTI to ensure a clean state for BlueOS
        let icr = uart_base.add(0x44 / 4);
        core::ptr::write_volatile(icr, (1 << 4) | (1 << 6));

        let imsc_val = core::ptr::read_volatile(imsc);
    }
}
