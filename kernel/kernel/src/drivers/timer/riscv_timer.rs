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

// A RISC-V timer is a hardware component, often memory-mapped, that provides
// timekeeping for the system, typically using the mtime register to count clock
// cycles and trigger interrupts (MTI) for tasks like operating system
// scheduling or precise event timing, enabling features like pulse-width
// modulation (PWM) or interval measurement by comparing mtime with a
// mtimecompare register.
pub trait RiscvTimer {
    const MTIME_PTR: usize;
    const MTIMECMP_BASE_PTR: usize;

    fn get_mtime() -> u64 {
        unsafe { core::ptr::read_volatile(Self::MTIME_PTR as *const u64) }
    }

    fn set_mtimecmp(hart: usize, deadline: u64) {
        let ptr = (Self::MTIMECMP_BASE_PTR + hart * 8) as *mut u64;
        unsafe { ptr.write_volatile(deadline) };
    }

    fn stop(hart: usize) {
        Self::set_mtimecmp(hart, u64::MAX)
    }
}
