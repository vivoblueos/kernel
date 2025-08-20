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

use super::ProcFileOps;
use crate::{
    error::Error,
    irq::irq_trace::{IrqTraceInfo, IRQ_COUNTERS, PER_CPU_TRACE_INFO},
    scheduler, thread, time,
};
use alloc::{string::String, vec::Vec};
use blueos_kconfig::NUM_CORES;
use core::{
    fmt::{self, Write},
    sync::atomic::Ordering::Relaxed,
};

pub(crate) struct SystemStat;

impl ProcFileOps for SystemStat {
    fn get_content(&self) -> Result<Vec<u8>, Error> {
        let cpu_time_str = format_cpu_time();
        let irq_counts_str = format_irq_counts();
        let mut result = String::with_capacity(cpu_time_str.len() + irq_counts_str.len() + 1);
        write!(result, "{}\n{}", cpu_time_str, irq_counts_str).unwrap();
        Ok(result.as_bytes().to_vec())
    }

    fn set_content(&self, content: Vec<u8>) -> Result<usize, Error> {
        Ok(0)
    }
}

#[derive(Default, Debug, Copy, Clone)]
struct CpuStat {
    cpu_id: usize,
    user: u64,
    nice: u64,
    system: u64,
    idle: u64,
    iowait: u64,
    irq: u64,
    softirq: u64,
    steal: u64,
    guest: u64,
    guest_nice: u64,
}

impl fmt::Display for CpuStat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.cpu_id == NUM_CORES {
            write!(
                f,
                "cpu {} {} {} {} {} {} {} {} {} {}",
                self.user,
                self.nice,
                self.system,
                self.idle,
                self.iowait,
                self.irq,
                self.softirq,
                self.steal,
                self.guest,
                self.guest_nice
            )
        } else {
            write!(
                f,
                "cpu{}  {} {} {} {} {} {} {} {} {} {}",
                self.cpu_id,
                self.user,
                self.nice,
                self.system,
                self.idle,
                self.iowait,
                self.irq,
                self.softirq,
                self.steal,
                self.guest,
                self.guest_nice
            )
        }
    }
}

fn format_cpu_time() -> String {
    let mut result = String::with_capacity(100 * (NUM_CORES + 1)); // total + every cpu core
    let mut total_system_time: u64 = 0;
    let mut total_idle_time: u64 = 0;
    let mut total_irq_time: u64 = 0;

    let mut cpu_stats = [CpuStat::default(); NUM_CORES + 1];
    loop {
        let pg = thread::Thread::try_preempt_me();
        if !pg.preemptable() {
            continue;
        }

        let total_cycle: u64 = time::get_sys_cycles();
        for cpu_id in 0..NUM_CORES {
            let idle_thread = scheduler::get_idle_thread(cpu_id);
            let idle_cycle = idle_thread.get_cycles();
            let system_time = time::get_cycles_to_ms(total_cycle.saturating_sub(idle_cycle)) / 10; // 10ms
            let idle_time = time::get_cycles_to_ms(idle_cycle) / 10;
            let irq_trace: &IrqTraceInfo = unsafe { &PER_CPU_TRACE_INFO[cpu_id] };
            let irq_time = time::get_cycles_to_ms(irq_trace.total_irq_process_cycles) / 10;
            total_system_time += system_time;
            total_idle_time += idle_time;
            total_irq_time += irq_time;
            cpu_stats[cpu_id + 1].cpu_id = cpu_id;
            cpu_stats[cpu_id + 1].system = system_time;
            cpu_stats[cpu_id + 1].idle = idle_time;
            cpu_stats[cpu_id + 1].irq = irq_time;
        }
        cpu_stats[0].cpu_id = NUM_CORES; // total
        cpu_stats[0].system = total_system_time;
        cpu_stats[0].idle = total_idle_time;
        cpu_stats[0].irq = total_irq_time;

        break;
    }

    for cpu_stat in &cpu_stats {
        write!(result, "{}", cpu_stat).unwrap();
    }
    result
}

fn format_irq_counts() -> String {
    let mut total_count: u64 = 0;
    let mut non_zero_count: usize = 0;
    for atomic in &IRQ_COUNTERS {
        let count = atomic.load(Relaxed) as u64;
        total_count = total_count.saturating_add(count);
        if count > 0 {
            non_zero_count += 1;
        }
    }
    const PREFIX: &str = "intr ";
    const U32_MAX_DIGITS: usize = 10;
    const LEN_PER_NON_ZERO_ELEMENT: usize = 1 + U32_MAX_DIGITS; // space + non-zero number
    const LEN_PER_ZERO_ELEMENT: usize = 2; // space + number 0
    let capacity = PREFIX.len()
        + LEN_PER_NON_ZERO_ELEMENT * non_zero_count
        + LEN_PER_ZERO_ELEMENT * (IRQ_COUNTERS.len() - non_zero_count);
    let mut result = String::with_capacity(capacity);
    write!(result, "{} {}", PREFIX, total_count).unwrap();
    for element in &IRQ_COUNTERS {
        let count = element.load(Relaxed);
        write!(result, " {}", count).unwrap();
    }
    result
}
