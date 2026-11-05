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

/// All four MPIDR affinity fields, excluding non-affinity flags.
pub(crate) const MPIDR_HWID_BITMASK: usize = 0xff00ffffff;

// A static array lets the entry assembly read the same mapping as Rust before
// a stack or the MMU is available. Board tables put the boot CPU first.
pub(crate) static CPU_AFFINITIES: [usize; blueos_kconfig::CONFIG_NUM_CORES as usize] = {
    let mut affinities = [0; blueos_kconfig::CONFIG_NUM_CORES as usize];
    assert!(!affinities.is_empty());
    assert!(affinities.len() <= crate::boards::CPU_AFFINITIES.len());
    let mut cpu = 0;
    while cpu < affinities.len() {
        let affinity = crate::boards::CPU_AFFINITIES[cpu];
        assert!(affinity & !MPIDR_HWID_BITMASK == 0);
        let mut previous = 0;
        while previous < cpu {
            assert!(affinities[previous] != affinity);
            previous += 1;
        }
        affinities[cpu] = affinity;
        cpu += 1;
    }
    affinities
};

#[inline]
pub(super) fn cpu_affinity(cpu_id: usize) -> usize {
    CPU_AFFINITIES[cpu_id]
}

#[inline]
pub(super) fn cpu_id_from_mpidr(mpidr: usize) -> Option<usize> {
    // Page-table bootstrap calls current_cpu_id() before the MMU is enabled.
    // PC-relative addressing follows the executing code's physical or virtual
    // mapping instead of loading the table's linked high virtual address.
    let affinities: *const usize;
    unsafe {
        core::arch::asm!(
            "adrp {addr}, {table}",
            "add {addr}, {addr}, :lo12:{table}",
            addr = out(reg) affinities,
            table = sym CPU_AFFINITIES,
            options(nostack, nomem, preserves_flags),
        );
        // SAFETY: the immutable array is loaded alongside the executing code.
        logical_cpu_id(
            core::slice::from_raw_parts(affinities, blueos_kconfig::CONFIG_NUM_CORES as usize),
            mpidr,
        )
    }
}

fn logical_cpu_id(affinities: &[usize], mpidr: usize) -> Option<usize> {
    let hwid = mpidr & MPIDR_HWID_BITMASK;
    affinities.iter().position(|&affinity| affinity == hwid)
}

/// Resolve MPIDR to a logical CPU ID in x9 without using a stack.
/// Clobbers x10..x13; an unconfigured CPU parks before accessing any CPU's stack.
#[macro_export]
macro_rules! aarch64_read_cpu_id {
    () => {
        "
        mrs x10, mpidr_el1
        ldr x13, ={mpidr_mask}
        and x10, x10, x13
        adrp x11, {cpu_affinities}
        add x11, x11, :lo12:{cpu_affinities}
        mov x9, #0
        mov x13, #{cpu_count}
        2:
        ldr x12, [x11, x9, lsl #3]
        cmp x12, x10
        b.eq 4f
        add x9, x9, #1
        cmp x9, x13
        b.lo 2b
        3:
        wfe
        b 3b
        4:
        "
    };
}

#[cfg(test)]
mod tests {
    use super::{cpu_affinity, cpu_id_from_mpidr, logical_cpu_id, CPU_AFFINITIES};
    use blueos_test_macro::test;

    #[test]
    fn cpu_topology_matches_platform_affinity() {
        for (cpu, &affinity) in CPU_AFFINITIES.iter().enumerate() {
            assert_eq!(cpu_affinity(cpu), crate::boards::CPU_AFFINITIES[cpu]);
            // M, U and MT are not part of the hardware affinity.
            assert_eq!(cpu_id_from_mpidr(0xc100_0000 | affinity), Some(cpu));
        }
    }

    #[test]
    fn logical_cpu_ids_support_sparse_affinities() {
        // A nonzero boot affinity and IDs spanning Aff0, Aff1, Aff2 and Aff3.
        let affinities = [0x200, 0x3, 0x50000, 0x1200000000];
        for (cpu, &affinity) in affinities.iter().enumerate() {
            assert_eq!(
                logical_cpu_id(&affinities, affinity | 0xc100_0000),
                Some(cpu)
            );
        }
        assert_eq!(logical_cpu_id(&affinities, 0), None);
        assert_eq!(logical_cpu_id(&affinities, 0x100000200), None);
        assert_eq!(logical_cpu_id(&[], 0), None);
    }
}
