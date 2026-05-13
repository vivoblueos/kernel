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

//! Memory region collection for coredump.
//!
//! Gathers PT_LOAD segments from linker symbols and thread stacks.
//! Uses only static slices — no heap allocation.

use crate::coredump::elf::MemSegment;

// ── Linker symbols ──────────────────────────────────────────────────────

extern "C" {
    static __bss_start: u8;
    static __bss_end: u8;
    static __sys_stack_start: u8;
    static __sys_stack_end: u8;
}

/// Dump mode: controls how much memory is collected.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum DumpMode {
    /// Current thread only (registers + current thread stack).
    Current,
    /// All thread stacks + system regions.
    Threads,
    /// Full RAM dump (all regions defined by the linker).
    Full,
}

/// Number of segment slots reserved in the segment array.
const MAX_SEGMENTS: usize = 32;

/// Collected memory segments and their count.
#[derive(Debug)]
pub struct RegionCollector {
    segments: [MemSegment; MAX_SEGMENTS],
    count: usize,
}

impl RegionCollector {
    pub const fn new() -> Self {
        Self {
            segments: [MemSegment {
                vaddr: 0,
                size: 0,
                data: &[],
                flags: 0,
            }; MAX_SEGMENTS],
            count: 0,
        }
    }

    fn push(&mut self, seg: MemSegment) {
        if self.count < MAX_SEGMENTS {
            self.segments[self.count] = seg;
            self.count += 1;
        }
    }

    pub fn segments(&self) -> &[MemSegment] {
        &self.segments[..self.count]
    }
}

/// Collect BSS region as a zero-fill segment.
fn collect_bss(col: &mut RegionCollector) {
    let start = unsafe { &__bss_start as *const u8 as usize };
    let end = unsafe { &__bss_end as *const u8 as usize };
    let size = end.saturating_sub(start);
    if size > 0 {
        col.push(MemSegment {
            vaddr: start,
            size,
            data: unsafe { core::slice::from_raw_parts(start as *const u8, size) },
            flags: 2, // PF_W
        });
    }
}

/// Collect system stack region.
fn collect_sys_stack(col: &mut RegionCollector) {
    let start = unsafe { &__sys_stack_start as *const u8 as usize };
    let end = unsafe { &__sys_stack_end as *const u8 as usize };
    let size = end.saturating_sub(start);
    if size > 0 {
        col.push(MemSegment {
            vaddr: start,
            size,
            data: unsafe { core::slice::from_raw_parts(start as *const u8, size) },
            flags: 3, // PF_R | PF_W
        });
    }
}

/// Collect the current thread's stack region.
fn collect_current_stack(col: &mut RegionCollector) {
    let thread = crate::scheduler::current_thread_ref();
    let base = thread.stack_base();
    let size = thread.stack_size();
    if size > 0 {
        col.push(MemSegment {
            vaddr: base,
            size,
            data: unsafe { core::slice::from_raw_parts(base as *const u8, size) },
            flags: 3,
        });
    }
}

/// Collect all thread stacks using the GlobalQueueVisitor API.
///
/// Iterates over every thread in the global queue, skipping RETIRED
/// threads (their stacks are freed). Each live thread's entire stack
/// region is added as a PT_LOAD segment.
fn collect_all_stacks(col: &mut RegionCollector) {
    use crate::thread::GlobalQueueVisitor;
    use crate::thread::RETIRED;

    let mut visitor = GlobalQueueVisitor::new();
    while let Some(thread_node) = visitor.next() {
        let thread = thread_node.lock();
        if thread.state() == RETIRED {
            continue;
        }
        let base = thread.stack_base();
        let size = thread.stack_size();
        if size > 0 && base != 0 {
            col.push(MemSegment {
                vaddr: base,
                size,
                data: unsafe { core::slice::from_raw_parts(base as *const u8, size) },
                flags: 3,
            });
        }
    }
}

/// Build the segment list for the given dump mode.
pub fn collect_regions(mode: DumpMode) -> RegionCollector {
    let mut col = RegionCollector::new();

    // System regions are always included.
    collect_bss(&mut col);
    collect_sys_stack(&mut col);

    match mode {
        DumpMode::Current => {
            collect_current_stack(&mut col);
        }
        DumpMode::Threads => {
            collect_all_stacks(&mut col);
        }
        DumpMode::Full => {
            collect_all_stacks(&mut col);
            // Full mode also collects BSS fully (already done above),
            // plus any additional heap regions (future).
        }
    }

    col
}