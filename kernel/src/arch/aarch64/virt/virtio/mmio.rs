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

use super::{VirtioDevice, VirtQueue, console::VirtioConsole};

pub struct VirtioMmioTransport<T: VirtioDevice> {
    pub device: T,
    pub status: u32,
    pub queue_sel: u32,
    pub devices_features_sel: u32,
    pub interrupt_status: u32,
    pub queues: [VirtQueue; 2],
    pub irq_handler: fn(),
}

impl<T: VirtioDevice> VirtioMmioTransport<T> {
    pub const fn new(device: T, irq_handler: fn()) -> Self {
        Self {
            device,
            status: 0,
            queue_sel: 0,
            devices_features_sel: 0,
            interrupt_status: 0,
            queues: [VirtQueue { ready: false, num: 0, desc_addr: 0, avail_addr: 0, used_addr: 0, last_idx: 0 }; 2],
            irq_handler,
        }
    }

    pub fn handle_read(&self, offset: u64) -> u32 {
        match offset {
            0x000 => 0x74726976,
            0x004 => 2,
            0x008 => self.device.device_id(),
            0x00c => self.device.vendor_id(),
            0x010 => {
                if self.devices_features_sel == 1 {
                    1
                } else {
                    0
                }
            }
            0x034 => 256,
            0x044 => if self.queue_sel < 2 { self.queues[self.queue_sel as usize].ready as u32 } else { 0 },
            0x60 => self.interrupt_status,
            0x070 => self.status,
            _ => 0,
        }
    }

    pub fn handle_write(&mut self, offset: u64, value: u32) {
        match offset {
            0x014 => self.devices_features_sel = value,
            0x030 => self.queue_sel = value,
            0x038 => if self.queue_sel < 2 { self.queues[self.queue_sel as usize].num = value },
            0x044 => if self.queue_sel < 2 { self.queues[self.queue_sel as usize].ready = value == 1 },
            0x050 => {
                let should_interrupt = self.device.handle_kick(value as usize, &mut self.queues);
                if should_interrupt {
                    self.interrupt_status |= 1;
                    (self.irq_handler)();
                }
            }
            0x064 => self.interrupt_status &= !value,
            0x070 => {
                self.status = value;
                self.device.handle_status(value);
            }
            0x080 => if self.queue_sel < 2 { self.queues[self.queue_sel as usize].desc_addr = (self.queues[self.queue_sel as usize].desc_addr & !0xFFFF_FFFF) | value as u64 },
            0x084 => if self.queue_sel < 2 { self.queues[self.queue_sel as usize].desc_addr = (self.queues[self.queue_sel as usize].desc_addr & 0xFFFF_FFFF) | ((value as u64) << 32) },
            0x090 => if self.queue_sel < 2 { self.queues[self.queue_sel as usize].avail_addr = (self.queues[self.queue_sel as usize].avail_addr & !0xFFFF_FFFF) | value as u64 },
            0x094 => if self.queue_sel < 2 { self.queues[self.queue_sel as usize].avail_addr = (self.queues[self.queue_sel as usize].avail_addr & 0xFFFF_FFFF) | ((value as u64) << 32) },
            0x0a0 => if self.queue_sel < 2 { self.queues[self.queue_sel as usize].used_addr = (self.queues[self.queue_sel as usize].used_addr & !0xFFFF_FFFF) | value as u64 },
            0x0a4 => if self.queue_sel < 2 { self.queues[self.queue_sel as usize].used_addr = (self.queues[self.queue_sel as usize].used_addr & 0xFFFF_FFFF) | ((value as u64) << 32) },
            _ => {}
        }
    }
}

impl VirtioMmioTransport<VirtioConsole> {
    pub fn inject_rx(&mut self, byte: u8) {
        if self.device.handle_rx(byte, &mut self.queues) {
            self.interrupt_status |= 1;
            // inject_irq(0, 48);
            (self.irq_handler)();

        }
    }
}