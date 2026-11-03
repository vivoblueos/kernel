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

//! Architecture-independent attributes requested for a virtual memory mapping.
//!
//! These types describe mapping requirements, not hardware descriptor bits.
//! A mapping backend must reject unsupported combinations rather than silently
//! grant additional access or weaken the requested memory semantics.
//!
//! Copy-on-write, shared/private mappings and backing storage belong to the
//! address space's mapping metadata. Present, accessed and dirty bits describe
//! page table state and are not configuration attributes here.

use bitflags::bitflags;

bitflags! {
    /// Access permissions and translation scope for a mapping.
    ///
    /// Bit positions are software definitions with no hardware encoding meaning.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct MemFlags: u8 {
        /// Allow data reads.
        const READ = 1 << 0;
        /// Allow data writes.
        const WRITE = 1 << 1;
        /// Allow instruction execution in the mapping's execution context.
        const EXECUTE = 1 << 2;
        /// Permit user-mode access according to READ, WRITE and EXECUTE.
        /// Without this flag, access is restricted to privileged code.
        const USER = 1 << 3;
        /// The mapping is identical across all address spaces and its translation
        /// may be retained across address-space switches. This is not a request
        /// for a shared process mapping; process-specific mappings must omit it.
        const GLOBAL = 1 << 4;
    }
}

/// Cache policy for normal memory, subject to architecture support.
///
/// These variants specify CPU caching behavior, not DMA coherency or barriers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CachePolicy {
    /// Cache reads and writes; modified cache lines may be written back later.
    WriteBack,
    /// Cache reads; writes also update memory without waiting for eviction.
    WriteThrough,
    /// Bypass normal caching and permit combining writes, for example to a
    /// framebuffer that tolerates this behavior.
    WriteCombining,
    /// Bypass normal caching. This remains normal memory and does not provide
    /// the access semantics required by device registers.
    Uncached,
}

/// Memory access semantics, independent of any architecture's attribute indices.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemType {
    /// Ordinary memory with an explicit cache policy.
    Normal(CachePolicy),
    /// Device registers: uncached, without speculative data accesses or write
    /// combining. This does not replace any device-required memory barriers.
    Device,
}

/// Desired properties of a virtual memory mapping.
///
/// READ, WRITE and EXECUTE are independent requests. Having none of them means
/// no access, even if USER or GLOBAL is set; it does not describe an accessible
/// page table entry. An architecture may need to leave such a mapping non-present.
///
/// Architecture code determines descriptor validity, privilege and execute-never
/// bits, cache encodings and hardware shareability from these requirements and
/// platform policy. This structure does not prescribe a page size or layout.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MemAttribute {
    /// Requested permissions and whether the translation is global.
    pub flags: MemFlags,
    /// Normal memory with a cache policy, or device memory.
    pub memory_type: MemType,
}
