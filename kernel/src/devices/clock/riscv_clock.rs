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

use crate::{arch, devices::clock::Clock, drivers::timers::RiscvTimer};

pub struct RiscvClock<const MTIME_PTR: usize, const MTIMECMP_BASE_PTR: usize, const HZ: u64>;

impl<const MTIME_PTR: usize, const MTIMECMP_BASE_PTR: usize, const HZ: u64> RiscvTimer
    for RiscvClock<MTIME_PTR, MTIMECMP_BASE_PTR, HZ>
{
    const MTIME_PTR: usize = MTIME_PTR;
    const MTIMECMP_BASE_PTR: usize = MTIMECMP_BASE_PTR;
}

impl<const MTIME_PTR: usize, const MTIMECMP_BASE_PTR: usize, const HZ: u64> Clock
    for RiscvClock<MTIME_PTR, MTIMECMP_BASE_PTR, HZ>
{
    fn hz() -> u64 {
        HZ
    }

    fn estimate_current_cycles() -> u64 {
        <Self as RiscvTimer>::get_mtime()
    }

    fn stop() {
        <Self as RiscvTimer>::stop(arch::current_cpu_id())
    }

    fn interrupt_at(deadline: u64) {
        <Self as RiscvTimer>::set_mtimecmp(arch::current_cpu_id(), deadline);
    }
}

pub type QemuRiscvClock = RiscvClock<0x0200_bff8, 0x0200_4000, 10_000_000>;
