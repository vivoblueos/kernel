// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
//       http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! ESP32-C6 出厂 MAC 地址读取(eFuse)。
//!
//! 与 C3 对比(基址不同,字段布局相同):
//! - EFUSE 基址:C6 = 0x600B_0800(C3 = 0x6000_8800)。来源 esp32c6-0.23.0
//!   pac crate lib.rs: `EFUSE = Periph<efuse::RegisterBlock, 0x600b_0800>`。
//! - rd_mac_spi_sys_0 偏移 0x044、_1 偏移 0x048:与 C3 完全一致
//!   (esp-idf esp32c6 efuse_reg.h: EFUSE_RD_MAC_SPI_SYS_0_REG = BASE + 0x44)。
//! - MAC 字段:reg0 的 mac_0 = MAC 低 32 位,reg1 的 mac_1[15:0] = MAC 高 16 位
//!   (esp-idf esp32c6 efuse_struct.h,bit 布局与 C3 完全相同)。
//! 因此字节拼装算法与 esp32c3.rs 一致,仅 EFUSE 基址不同。

use crate::static_ref::StaticRef;
use tock_registers::{interfaces::Readable, register_structs, registers::ReadOnly};

// C6 的 EFUSE 控制器基址(与 C3 的 0x6000_8800 不同,C6 移到 0x600B_xxxx 段)。
const EFUSE_BASE: usize = 0x600B_0800;

register_structs! {
    /// C6 eFuse 控制器读数据寄存器块(只列 MAC 相关字段,偏移与 C3 相同)。
    EfuseRegisters {
        (0x00 => _reserved0),
        /// BLOCK1 数据寄存器 0:mac_0 = MAC 低 32 位。
        (0x044 => rd_mac_spi_sys_0: ReadOnly<u32>),
        /// BLOCK1 数据寄存器 1:mac_1[15:0] = MAC 高 16 位。
        (0x048 => rd_mac_spi_sys_1: ReadOnly<u32>),
        (0x04C => @END),
    }
}

static EFUSE_REGISTERS: StaticRef<EfuseRegisters> =
    unsafe { StaticRef::new(EFUSE_BASE as *const EfuseRegisters) };

/// 读取芯片出厂烧录的 MAC 地址(6 字节)。
///
/// 字节顺序(与 C3 相同,因 MAC 字段 bit 布局一致):
/// reg1 的高 2 字节(mac_1 的小端低 2 字节)在 MAC 的高 2 位,
/// reg0 的 4 字节按小端逆序填入 MAC 的低 4 位。
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
