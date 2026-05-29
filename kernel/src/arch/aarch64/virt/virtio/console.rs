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

use core::sync::atomic::{compiler_fence, Ordering};
use super::{VirtioDevice, VirtQueue, VirtqDesc, VirtqAvail, VirtqUsed};
use crate::{kprintln, kearly_println};

pub struct VirtioConsole;

impl VirtioConsole {
    pub const fn new() -> Self { Self }

    pub fn handle_rx(&mut self, byte: u8, queues: &mut [VirtQueue]) -> bool {
        // RX Queue is index 0.
        let q_idx = 0;
        let q = &mut queues[q_idx];
        
        if !q.ready || q.desc_addr == 0 { return false; }

        unsafe {
            let avail = q.avail_addr as *const VirtqAvail;
            let used  = q.used_addr as *mut VirtqUsed;
            let desc_table = q.desc_addr as *const VirtqDesc;
            if q.last_idx == (*avail).idx { return false; }

            let ring_index = (q.last_idx % q.num as u16) as usize;
            let head = (*avail).ring[ring_index] as usize;
            let desc = &(*desc_table.add(head));
            let payload_ptr = desc.addr as *mut u8;
            *payload_ptr = byte;
            let u_idx = ((*used).idx % q.num as u16) as usize;
            (*used).ring[u_idx].id = head as u32;
            (*used).ring[u_idx].len = 1;
            core::arch::asm!("dmb ishst", options(nostack));
            (*used).idx = (*used).idx.wrapping_add(1);
            q.last_idx = q.last_idx.wrapping_add(1);
            core::arch::asm!("dsb ishst", options(nostack));
        }
        true
    }
}

impl VirtioDevice for VirtioConsole {
    fn device_id(&self) -> u32 { 3 }
    fn vendor_id(&self) -> u32 { 0x424C5545 }
    fn handle_status(&mut self, _status: u32) {}

    fn handle_kick(&mut self, q_idx: usize, queues: &mut [VirtQueue]) -> bool {
        // TX Queue is index 1.
        if q_idx != 1 {
            return false;
        }
        
        let q = &mut queues[q_idx];
        if !q.ready || q.desc_addr == 0 {
            return false;
        }

        let mut processed = false;
        unsafe {
            let desc_table = q.desc_addr as *const VirtqDesc;
            let avail_ring = q.avail_addr as *const VirtqAvail;
            let used_ring  = q.used_addr as *mut VirtqUsed;

            while q.last_idx != (*avail_ring).idx {
                processed = true;
                let ring_index = (q.last_idx % q.num as u16) as usize;
                let head = (*avail_ring).ring[ring_index] as usize;
                let desc = &(*desc_table.add(head));
                let slice = core::slice::from_raw_parts(desc.addr as *const u8, desc.len as usize);
                if let Ok(s) = core::str::from_utf8(slice) {
                    for byte in s.as_bytes() {
                        let mut writer = crate::console::EarlyConsole {};
                        use core::fmt::Write;
                        writer.write_str(core::str::from_utf8(&[*byte]).unwrap_or("")).unwrap();
                    }
                }

                let u_idx = ((*used_ring).idx % q.num as u16) as usize;
                (*used_ring).ring[u_idx].id = head as u32;
                (*used_ring).ring[u_idx].len = 0;
                unsafe {
                    core::arch::asm!("dmb ishst", options(nostack)); 
                    (*used_ring).idx = (*used_ring).idx.wrapping_add(1);
                    q.last_idx = q.last_idx.wrapping_add(1);
                    core::arch::asm!("dsb ishst", options(nostack)); 
                }
            }
        }
        processed
    }
}