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

use crate::{devices::clock::Clock, drivers::timers::GenericTimer};

pub struct GenericClock;

impl Clock for GenericClock {
    fn hz() -> u64 {
        GenericTimer::read_cntfrq()
    }

    fn estimate_current_cycles() -> u64 {
        GenericTimer::read_cntpct()
    }

    fn interrupt_at(moment: u64) {
        GenericTimer::write_cntp_cval(moment);
        // ENABLE(1) | IMASK(0) = 1
        GenericTimer::write_cntp_ctl(1);
    }

    fn stop() {
        GenericTimer::write_cntp_ctl(0);
    }
}

pub type QemuGtClk = GenericClock;
