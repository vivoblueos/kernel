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

//! ESP32-C6 factory MAC address readout (eFuse).
//!
//! Comparison with C3 (base differs, field layout identical):
//! - EFUSE base: C6 = 0x600B_0800 (C3 = 0x6000_8800). Source: esp32c6-0.23.0
//!   pac crate lib.rs: `EFUSE = Periph<efuse::RegisterBlock, 0x600b_0800>`.
//! - rd_mac_spi_sys_0 offset 0x044, _1 offset 0x048: identical to C3
//!   (esp-idf esp32c6 efuse_reg.h: EFUSE_RD_MAC_SPI_SYS_0_REG = BASE + 0x44).
//! - MAC fields: reg0's mac_0 = MAC low 32 bits, reg1's mac_1[15:0] = MAC high 16 bits
//!   (esp-idf esp32c6 efuse_struct.h; bit layout identical to C3).
//! Hence the byte-assembly algorithm matches esp32c3.rs; only the EFUSE base differs.

use crate::static_ref::StaticRef;
use tock_registers::{interfaces::Readable, register_structs, registers::ReadOnly};

// C6 EFUSE controller base (unlike C3's 0x6000_8800, C6 moved it to the 0x600B_xxxx segment).
const EFUSE_BASE: usize = 0x600B_0800;

register_structs! {
    /// C6 eFuse controller read-data register block (only MAC-relevant fields listed; offsets match C3).
    EfuseRegisters {
        (0x00 => _reserved0),
        /// BLOCK1 data register 0: mac_0 = MAC low 32 bits.
        (0x044 => rd_mac_spi_sys_0: ReadOnly<u32>),
        /// BLOCK1 data register 1: mac_1[15:0] = MAC high 16 bits.
        (0x048 => rd_mac_spi_sys_1: ReadOnly<u32>),
        (0x04C => @END),
    }
}

static EFUSE_REGISTERS: StaticRef<EfuseRegisters> =
    unsafe { StaticRef::new(EFUSE_BASE as *const EfuseRegisters) };

/// Read the chip factory-burned MAC address (6 bytes).
///
/// Byte order (same as C3, since the MAC field bit layout matches):
/// reg1's high 2 bytes (the little-endian low 2 bytes of mac_1) occupy the top 2 bytes of MAC,
/// reg0's 4 bytes fill the low 4 bytes of MAC in little-endian reverse order.
pub fn mac() -> [u8; 6] {
    let mac0 = EFUSE_REGISTERS.rd_mac_spi_sys_0.get();
    let mac1 = EFUSE_REGISTERS.rd_mac_spi_sys_1.get();

    let mac1_bytes = mac1.to_le_bytes();
    let mac0_bytes = mac0.to_le_bytes();

    [
        mac1_bytes[1],
        mac1_bytes[0],
        mac0_bytes[3],
        mac0_bytes[2],
        mac0_bytes[1],
        mac0_bytes[0],
    ]
}
