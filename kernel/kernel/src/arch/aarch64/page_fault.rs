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

use aarch64_cpu::registers::ESR_EL1;

/// Fault class encoded in FSC[3:2] for the level 0–3 page-table faults.
#[derive(Debug, Clone, Copy, PartialEq, Eq, num_derive::FromPrimitive)]
#[repr(u8)]
pub(super) enum PageFaultKind {
    AddressSize = 0b00,
    Translation = 0b01,
    AccessFlag = 0b10,
    Permission = 0b11,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum FaultAccess {
    Execute,
    Read,
    Write,
    CacheMaintenanceOrAddressTranslation,
}

impl FaultAccess {
    fn from_data_abort(iss: u64) -> Self {
        const CM: u64 = 1 << 8;
        const WNR: u64 = 1 << 6;
        if iss & CM != 0 {
            Self::CacheMaintenanceOrAddressTranslation
        } else if iss & WNR != 0 {
            Self::Write
        } else {
            Self::Read
        }
    }
}

/// Snapshot of an instruction or data page fault taken to EL1.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct PageFaultInfo {
    pub(super) kind: PageFaultKind,
    /// FSC[1:0]. For an address size fault, zero can also indicate a TTBR fault.
    pub(super) level: u8,
    pub(super) access: FaultAccess,
    /// Virtual address reported by FAR_EL1.
    pub(super) fault_address: u64,
}

impl PageFaultInfo {
    pub(super) fn decode(esr: u64, read_far: impl FnOnce() -> u64) -> Option<Self> {
        use ESR_EL1::EC::Value::*;

        let iss = ESR_EL1::ISS.read(esr);
        let access = match ESR_EL1::EC.read_as_enum(esr)? {
            InstrAbortLowerEL | InstrAbortCurrentEL => FaultAccess::Execute,
            DataAbortLowerEL | DataAbortCurrentEL => FaultAccess::from_data_abort(iss),
            _ => return None,
        };
        let fsc = (iss & 0x3f) as u8;
        Some(Self {
            kind: num_traits::FromPrimitive::from_u8(fsc >> 2)?,
            level: fsc & 0b11,
            access,
            fault_address: read_far(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn decodes_abort_context() {
        for (ec, iss, access) in [
            (0x20, 0x07, FaultAccess::Execute),
            (0x21, 0x07, FaultAccess::Execute),
            (0x24, 0x07, FaultAccess::Read),
            (0x25, 0x47, FaultAccess::Write),
            (
                0x25,
                0x147,
                FaultAccess::CacheMaintenanceOrAddressTranslation,
            ),
        ] {
            let esr = (ec << 26) | iss;
            assert_eq!(
                PageFaultInfo::decode(esr, || 0xc000),
                Some(PageFaultInfo {
                    kind: PageFaultKind::Translation,
                    level: 3,
                    access,
                    fault_address: 0xc000,
                })
            );
        }
    }

    #[test]
    fn distinguishes_page_faults_from_other_syndromes() {
        let data_abort = 0x25 << 26;
        let kinds = [
            PageFaultKind::AddressSize,
            PageFaultKind::Translation,
            PageFaultKind::AccessFlag,
            PageFaultKind::Permission,
        ];
        for fsc in 0..64 {
            let fault = PageFaultInfo::decode(data_abort | fsc, || {
                assert!(fsc < 16);
                0
            });
            assert_eq!(
                fault.map(|f| (f.kind, f.level)),
                kinds
                    .get((fsc / 4) as usize)
                    .map(|&kind| (kind, (fsc % 4) as u8))
            );
        }
        assert!(PageFaultInfo::decode((0x15 << 26) | 0x07, || unreachable!()).is_none());
    }
}
