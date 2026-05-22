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

pub mod console;
pub mod mmio;

pub use console::VirtioConsole;
pub use mmio::VirtioMmioTransport;
use crate::arch::virt::vgic::inject_irq;

fn console_irq_handler() {
    inject_irq(0, 48);
}

pub static mut VIRTIO_CONSOLE: VirtioMmioTransport<VirtioConsole> = 
    VirtioMmioTransport::new(VirtioConsole::new(), console_irq_handler);

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct VirtqDesc {
    pub addr: u64,
    pub len: u32,
    pub flags: u16,
    pub next: u16,
}

#[repr(C)]
pub struct VirtqAvail {
    pub flags: u16,
    pub idx: u16,
    pub ring: [u16; 256],
}

#[repr(C)]
pub struct VirtqUsedElem {
    pub id: u32,
    pub len: u32,
}

#[repr(C)]
pub struct VirtqUsed {
    pub flags: u16,
    pub idx: u16,
    pub ring: [VirtqUsedElem; 256],
}

#[derive(Default, Clone, Copy)]
pub struct VirtQueue {
    pub ready: bool,
    pub num: u32,
    pub desc_addr: u64,
    pub avail_addr: u64,
    pub used_addr: u64,
    pub last_idx: u16,
}

pub trait VirtioDevice {
    fn device_id(&self) -> u32;
    fn vendor_id(&self) -> u32;
    fn handle_status(&mut self, status: u32);
    fn handle_kick(&mut self, q_idx: usize, queues: &mut [VirtQueue]) -> bool; 
}