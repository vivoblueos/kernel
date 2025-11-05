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

#[derive(Debug)]
#[repr(u32)]
pub enum PsciFuncName {
    Version = 0,
    CpuSuspend = 1,
    CpuOff = 2,
    CpuOn = 3,
    AffinityInfo = 4,
    Migrate = 5,
    MigrateInfoType = 6,
    MigrateInfoUpCpu = 7,
    SystemOff = 8,
    SystemReset = 9,
}

// Return the version of PSCI implemented
pub fn get_psci_version(psci_base: u32) -> usize {
    let func_id = psci_base + (PsciFuncName::Version as u32);
    unsafe { psci_call(func_id, 0, 0, 0, 0, 0, 0, 0) }
}

// Suspend execution on a core or higher-level topology node.
//
// # Arguments
//
// * `power_state` - The power state.
// * `entry` - The entry poin.
// * `context_id` - The context id, this value must be present in X0
// *  Entry and context_id is only valid if the target power state is a powerdown state.
// *  For standby states, the value passed in is ignored.
pub fn cpu_suspend(psci_base: u32, power_state: usize, entry: usize, context_id: usize) {
    let func_id = psci_base + (PsciFuncName::CpuSuspend as u32);
    unsafe {
        psci_call(func_id, power_state, entry, context_id, 0, 0, 0, 0);
    }
}

/// Power down the calling core, this call is intended for use in hotplug.
pub fn cpu_off(psci_base: u32) {
    let func_id = psci_base + (PsciFuncName::CpuOff as u32);
    unsafe {
        psci_call(func_id, 0, 0, 0, 0, 0, 0, 0);
    }
}

// Power up a core. This call is used to power up cores that eithe:
//     1.Have not yet been booted into the calling supervisory software.
//     2.Have been previously powered down with a CPU_OFF call.
//
// # Arguments
//
// * `target_cpu` - This parameter contains a copy of the affinity fields of the MPIDR registe.
//     If the calling Exception level is using AArch64, the format is:
//        - Bits[40:63]: Must be zero
//        - Bits[32:39] Aff3: Match Aff3 of target core MPIDR
//        - Bits[24:31] Must be zero
//        - Bits[16:23] Aff2: Match Aff2 of target core MPIDR
//        - Bits[8:15] Aff1: Match Aff1 of target core MPIDR
//        - Bits[0:7] Aff0: Match Aff0 of target core MPIDR
// * `entry` - The entry poin.
// * `context_id` - The context id, this value must be present in X0
pub fn cpu_on(psci_base: u32, target_cpu: usize, entry: usize, context_id: usize) {
    let func_id = psci_base + (PsciFuncName::CpuOn as u32);
    unsafe {
        psci_call(
            func_id,
            target_cpu & 0xff00ffffff,
            entry,
            context_id,
            0,
            0,
            0,
            0,
        );
    }
}

// Enable the caller to request status of an affinity instance
//
// # Arguments
//
// * `target_affinity` - This follows the same format as the target_cpu parameter of a CPU_ON.
// * `lowest_affinity_level` - Denotes the lowest affinity level field that is valid in the target_affinity parameter.
pub fn affinity_info(
    psci_base: u32,
    target_affinity: usize,
    lowest_affinity_level: usize,
) -> usize {
    let func_id = psci_base + (PsciFuncName::AffinityInfo as u32);
    unsafe {
        psci_call(
            func_id,
            target_affinity & 0xff00ffffff,
            lowest_affinity_level,
            0,
            0,
            0,
            0,
            0,
        )
    }
}

// This is used to ask a uniprocessor Trusted OS to migrate its context to a specific core
//
// # Arguments
//
// * `target_cpu` - This parameter contains a copy of the affinity fields of the MPIDR registe.
pub fn migrate(psci_base: u32, target_cpu: usize) {
    let func_id = psci_base + (PsciFuncName::Migrate as u32);
    unsafe {
        psci_call(func_id, target_cpu & 0xff00ffffff, 0, 0, 0, 0, 0, 0);
    }
}

// This function allows a caller to identify the level of multicore support present in the Trusted OS.
pub fn migrate_info_type(psci_base: u32) -> usize {
    let func_id = psci_base + (PsciFuncName::MigrateInfoType as u32);
    unsafe { psci_call(func_id, 0, 0, 0, 0, 0, 0, 0) }
}

// For a uniprocessor Trusted OS, this function returns the current resident core.
pub fn migrate_info_up_cpu(psci_base: u32) -> usize {
    let func_id = psci_base + (PsciFuncName::MigrateInfoUpCpu as u32);
    unsafe { psci_call(func_id, 0, 0, 0, 0, 0, 0, 0) }
}

// Shut down the system.
pub fn system_off(psci_base: u32) -> ! {
    let func_id = psci_base + (PsciFuncName::SystemOff as u32);
    unsafe {
        psci_call(func_id, 0, 0, 0, 0, 0, 0, 0);
    }
    core::unreachable!()
}

// Reset the system
pub fn system_reset(psci_base: u32) -> ! {
    let func_id = psci_base + (PsciFuncName::SystemReset as u32);
    unsafe {
        psci_call(func_id, 0, 0, 0, 0, 0, 0, 0);
    }
    core::unreachable!()
}

#[inline]
unsafe extern "C" fn psci_call(
    func_id: u32,
    arg0: usize,
    arg1: usize,
    arg2: usize,
    arg3: usize,
    arg4: usize,
    arg5: usize,
    arg6: usize,
) -> usize {
    let ret: usize;
    core::arch::asm!(
        // Select the calling method according to PSCI implementation
        "smc #0",
        inlateout("x0") func_id as usize => ret,
        inlateout("x1") arg0 => _,
        in("x2") arg1,
        in("x3") arg2,
        in("x4") arg3,
        in("x5") arg4,
        in("x6") arg5,
        in("x7") arg6,
        options(nostack)
    );
    ret
}
