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

//! Trusted ELF architecture and ABI profiles supplied by the caller.
//! These describe policy; ELF admission is added in the next stage.

use goblin::elf::header::{ELFCLASS32, ELFCLASS64, ELFDATA2LSB, ELFDATA2MSB, EM_AARCH64, EM_RISCV};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ElfClass {
    Elf32,
    Elf64,
}

impl From<ElfClass> for u64 {
    fn from(value: ElfClass) -> Self {
        match value {
            ElfClass::Elf32 => u64::from(ELFCLASS32),
            ElfClass::Elf64 => u64::from(ELFCLASS64),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ElfData {
    Little,
    Big,
}

impl From<ElfData> for u64 {
    fn from(value: ElfData) -> Self {
        match value {
            ElfData::Little => u64::from(ELFDATA2LSB),
            ElfData::Big => u64::from(ELFDATA2MSB),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ElfMachine {
    Riscv,
    Aarch64,
    Other(u16),
}

impl From<ElfMachine> for u64 {
    fn from(value: ElfMachine) -> Self {
        match value {
            ElfMachine::Riscv => u64::from(EM_RISCV),
            ElfMachine::Aarch64 => u64::from(EM_AARCH64),
            ElfMachine::Other(x) => u64::from(x),
        }
    }
}

/// RISC-V `e_flags` bits the loader interprets. The float ABI must be soft for
/// the current RISC-V profiles; the embedded (RVE) register model is unsupported.
const EF_RISCV_FLOAT_ABI_MASK: u32 = 0x0000_0006;
const EF_RISCV_FLOAT_ABI_SOFT: u32 = 0x0000_0000;
const EF_RISCV_RVE: u32 = 0x0000_0008;

/// Bit-level `e_flags` admission policy for one ELF machine.
///
/// `e_flags` is machine-defined; a policy only ever names the bits its
/// profile understands, so an unknown flag is never interpreted across
/// architectures. A header's flags are accepted when every `required` bit is
/// set, every `forbidden` bit is clear, and the `mask`-selected bits equal
/// `required`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct HeaderFlagsPolicy {
    mask: u32,
    required: u32,
    forbidden: u32,
}

impl HeaderFlagsPolicy {
    #[inline]
    pub const fn new(mask: u32, required: u32, forbidden: u32) -> Self {
        Self {
            mask,
            required,
            forbidden,
        }
    }

    /// Check the machine-specific flags against the profile constraints.
    #[inline]
    pub const fn accepts(self, flags: u32) -> bool {
        (flags & self.mask) == self.required && (flags & self.forbidden) == 0
    }
}

/// Native entry address alignment and the minimum instruction span.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EntryMode {
    Direct {
        instruction_alignment: u8,
        minimum_instruction_size: u8,
    },
}

impl EntryMode {
    #[inline]
    pub const fn direct(instruction_alignment: u8, minimum_instruction_size: u8) -> Self {
        Self::Direct {
            instruction_alignment,
            minimum_instruction_size,
        }
    }

    #[inline]
    pub const fn instruction_alignment(self) -> u8 {
        match self {
            Self::Direct {
                instruction_alignment,
                ..
            } => instruction_alignment,
        }
    }

    #[inline]
    pub const fn minimum_instruction_size(self) -> u8 {
        match self {
            Self::Direct {
                minimum_instruction_size,
                ..
            } => minimum_instruction_size,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LoadProfile {
    class: ElfClass,
    endian: ElfData,
    machine: ElfMachine,
    header_flags: HeaderFlagsPolicy,
    entry_mode: EntryMode,
}

impl LoadProfile {
    #[inline]
    pub const fn new(
        class: ElfClass,
        endian: ElfData,
        machine: ElfMachine,
        header_flags: HeaderFlagsPolicy,
        entry_mode: EntryMode,
    ) -> Self {
        Self {
            class,
            endian,
            machine,
            header_flags,
            entry_mode,
        }
    }

    /// AArch64 little-endian ELF profile with a native aligned entry.
    #[inline]
    pub const fn aarch64() -> Self {
        Self::new(
            ElfClass::Elf64,
            ElfData::Little,
            ElfMachine::Aarch64,
            HeaderFlagsPolicy::new(u32::MAX, 0, 0),
            EntryMode::direct(4, 4),
        )
    }

    /// RISC-V RV32 soft-float profile (RVC permitted, RVE rejected).
    #[inline]
    pub const fn riscv32() -> Self {
        Self::new(
            ElfClass::Elf32,
            ElfData::Little,
            ElfMachine::Riscv,
            HeaderFlagsPolicy::new(
                EF_RISCV_FLOAT_ABI_MASK,
                EF_RISCV_FLOAT_ABI_SOFT,
                EF_RISCV_RVE,
            ),
            EntryMode::direct(2, 2),
        )
    }

    /// RISC-V RV64 soft-float profile (RVC permitted, RVE rejected).
    #[inline]
    pub const fn riscv64() -> Self {
        Self::new(
            ElfClass::Elf64,
            ElfData::Little,
            ElfMachine::Riscv,
            HeaderFlagsPolicy::new(
                EF_RISCV_FLOAT_ABI_MASK,
                EF_RISCV_FLOAT_ABI_SOFT,
                EF_RISCV_RVE,
            ),
            EntryMode::direct(2, 2),
        )
    }

    #[inline]
    pub const fn class(&self) -> ElfClass {
        self.class
    }

    #[inline]
    pub const fn endian(&self) -> ElfData {
        self.endian
    }

    #[inline]
    pub const fn machine(&self) -> ElfMachine {
        self.machine
    }

    #[inline]
    pub const fn header_flags(&self) -> HeaderFlagsPolicy {
        self.header_flags
    }

    #[inline]
    pub const fn entry_mode(&self) -> EntryMode {
        self.entry_mode
    }
}
