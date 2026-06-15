// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
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

use crate::{arch, kprintln, scheduler, time};
use logger_crate::LoggerHooks;

/// log init
pub fn logger_init() {
    static HOOKS: LoggerHooks = LoggerHooks {
        timestamp_ms: || time::now().as_millis(),
        cpu_id: || arch::current_cpu_id(),
        thread_id: || scheduler::current_thread_id(),
        write: |line| {
            #[cfg(not(test))]
            kprintln!("{}", line.trim_end());
            #[cfg(test)]
            semihosting::println!("{}", line.trim_end());
        },
    };
    logger_crate::logger_init(&HOOKS);
}
