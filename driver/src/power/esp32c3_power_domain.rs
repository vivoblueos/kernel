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

use crate::static_ref::StaticRef;
use tock_registers::{
    interfaces::ReadWriteable, register_bitfields, register_structs, registers::ReadWrite,
};

register_structs! {
    Registers {
        (0x00 => _reserved0),
        (0x88 => dig_pwc: ReadWrite<u32, RTC_CNTL_DIG_PWC::Register>),
        (0x8C => dig_iso: ReadWrite<u32, RTC_CNTL_DIG_ISO::Register>),
        (0x90 => @END),
    }
}

register_bitfields! [u32,
    /// RTC_CNTL_DIG_PWC_REG (0x0088): Digital Power Control Register
    /// Controls power domain states for various subsystems during sleep/wake.
    /// Reset value: 0x0. Access: R/W
    RTC_CNTL_DIG_PWC [
        /// VDD_SPI power drive control. Controls the drive capability of vdd_spi. R/W
        RTC_CNTL_VDD_SPI_PWR_DRV OFFSET(0) NUMBITS(2),
        /// Force VDD_SPI power drive. Write 1 to force VDD_SPI driver output. R/W
        RTC_CNTL_VDD_SPI_PWR_FORCE OFFSET(2) NUMBITS(1),
        /// Force LSLP memory power down. Write 1 to prevent retention during sleep. R/W
        RTC_CNTL_LSLP_MEM_FORCE_PD OFFSET(3) NUMBITS(1),
        /// Force LSLP memory power up. Write 1 to force retention during sleep. R/W
        RTC_CNTL_LSLP_MEM_FORCE_PU OFFSET(4) NUMBITS(1),
        /// Force digital peripheral power down. Write 1 to power down peripherals. R/W
        RTC_CNTL_DG_PERI_FORCE_PD OFFSET(13) NUMBITS(1),
        /// Force digital peripheral power up. Write 1 to power up peripherals. R/W
        RTC_CNTL_DG_PERI_FORCE_PU OFFSET(14) NUMBITS(1),
        /// Force FASTMEM power down for low power. Write 1 to power down fast memory. R/W
        RTC_CNTL_FASTMEM_FORCE_LPD OFFSET(15) NUMBITS(1),
        /// Force FASTMEM power up for low power. Write 1 to force retention in fast memory. R/W
        RTC_CNTL_FASTMEM_FORCE_LPU OFFSET(16) NUMBITS(1),
        /// Force WiFi module power down. Write 1 to power down wireless module. R/W
        RTC_CNTL_WIFI_FORCE_PD OFFSET(17) NUMBITS(1),
        /// Force WiFi module power up. Write 1 to power up wireless module. R/W
        RTC_CNTL_WIFI_FORCE_PU OFFSET(18) NUMBITS(1),
        /// Force digital wrap power down. Write 1 to power down digital system. R/W
        RTC_CNTL_DG_WRAP_FORCE_PD OFFSET(19) NUMBITS(1),
        /// Force digital wrap power up. Write 1 to power up digital system. R/W
        RTC_CNTL_DG_WRAP_FORCE_PU OFFSET(20) NUMBITS(1),
        /// Force CPU TOP power down. Write 1 to power down CPU domain. R/W
        RTC_CNTL_CPU_TOP_FORCE_PD OFFSET(21) NUMBITS(1),
        /// Force CPU TOP power up. Write 1 to power up CPU domain. R/W
        RTC_CNTL_CPU_TOP_FORCE_PU OFFSET(22) NUMBITS(1),
        /// Enable digital peripheral power down in sleep. Write 1 to enable power-down. R/W
        RTC_CNTL_DG_PERI_PD_EN OFFSET(28) NUMBITS(1),
        /// Enable CPU TOP power down in sleep. Write 1 to enable power-down. R/W
        RTC_CNTL_CPU_TOP_PD_EN OFFSET(29) NUMBITS(1),
        /// Enable WiFi power down in sleep. Write 1 to enable power-down. R/W
        RTC_CNTL_WIFI_PD_EN OFFSET(30) NUMBITS(1),
        /// Enable digital wrap power down in sleep. Write 1 to enable power-down. R/W
        RTC_CNTL_DG_WRAP_PD_EN OFFSET(31) NUMBITS(1),
    ],

    /// RTC_CNTL_DIG_ISO_REG (0x008C): Digital Isolation Control Register
    /// Controls isolation state for digital domains and pads during sleep/low-power modes.
    /// Reset value: 0x0. Access: R/W
    RTC_CNTL_DIG_ISO [
        /// Force digital wrap system out of isolation. Write 1 to disable isolation. R/W
        RTC_CNTL_DG_WRAP_FORCE_NOISO OFFSET(31) NUMBITS(1),
        /// Force digital wrap system into isolation. Write 1 to enable isolation. R/W
        RTC_CNTL_DG_WRAP_FORCE_ISO OFFSET(30) NUMBITS(1),
        /// Force wireless module out of isolation. Write 1 to disable isolation. R/W
        RTC_CNTL_WIFI_FORCE_NOISO OFFSET(29) NUMBITS(1),
        /// Force wireless module into isolation. Write 1 to enable isolation. R/W
        RTC_CNTL_WIFI_FORCE_ISO OFFSET(28) NUMBITS(1),
        /// Force CPU TOP domain out of isolation. Write 1 to disable isolation. R/W
        RTC_CNTL_CPU_TOP_FORCE_NOISO OFFSET(27) NUMBITS(1),
        /// Force CPU TOP domain into isolation. Write 1 to enable isolation. R/W
        RTC_CNTL_CPU_TOP_FORCE_ISO OFFSET(26) NUMBITS(1),
        /// Force digital peripherals out of isolation. Write 1 to disable isolation. R/W
        RTC_CNTL_DG_PERI_FORCE_NOISO OFFSET(25) NUMBITS(1),
        /// Force digital peripherals into isolation. Write 1 to enable isolation. R/W
        RTC_CNTL_DG_PERI_FORCE_ISO OFFSET(24) NUMBITS(1),
        /// Force digital GPIO pads into hold state. Write 1 to latch pad output. R/W
        RTC_CNTL_DG_PAD_FORCE_HOLD OFFSET(15) NUMBITS(1),
        /// Force digital GPIO pads out of hold state. Write 1 to release latched output. R/W
        RTC_CNTL_DG_PAD_FORCE_UNHOLD OFFSET(14) NUMBITS(1),
        /// Force digital GPIO pads into isolation. Write 1 to enable isolation. R/W
        RTC_CNTL_DG_PAD_FORCE_ISO OFFSET(13) NUMBITS(1),
        /// Force digital GPIO pads out of isolation. Write 1 to disable isolation. R/W
        RTC_CNTL_DG_PAD_FORCE_NOISO OFFSET(12) NUMBITS(1),
        /// Enable auto-hold for digital GPIO pads. Write 1 to enable automatic latching. R/W
        RTC_CNTL_DG_PAD_AUTOHOLD_EN OFFSET(11) NUMBITS(1),
        /// Clear auto-hold for digital GPIO pads. Write 1 to clear auto-hold state. WO
        RTC_CNTL_CLR_DG_PAD_AUTOHOLD OFFSET(10) NUMBITS(1),
        /// Digital GPIO pad auto-hold state indicator. Read to check if pads are held. RO
        RTC_CNTL_DG_PAD_AUTOHOLD OFFSET(9) NUMBITS(1),
    ],
];

pub struct PowerDomain {
    inner: StaticRef<Registers>,
}

impl PowerDomain {
    pub const fn new(base_addr: usize) -> Self {
        PowerDomain {
            inner: unsafe { StaticRef::new(base_addr as *const Registers) },
        }
    }

    pub fn enable_wifi(&self) {
        self.inner
            .dig_pwc
            .modify(RTC_CNTL_DIG_PWC::RTC_CNTL_WIFI_FORCE_PD::CLEAR);

        // modified from https://github.com/esp-rs/esp-hal/blob/63ff86ca206fc1bd25699527ed30094f3bb9a872/esp-radio/src/common_adapter.rs#L339-L365
        unsafe {
            const WIFIBB_RST: u32 = 1 << 0; // Wi-Fi baseband
            const FE_RST: u32 = 1 << 1; // RF Frontend RST
            const WIFIMAC_RST: u32 = 1 << 2; // Wi-Fi MAC

            const BTBB_RST: u32 = 1 << 3; // Bluetooth Baseband
            const BTMAC_RST: u32 = 1 << 4; // deprecated
            const RW_BTMAC_RST: u32 = 1 << 9; // Bluetooth MAC
            const RW_BTMAC_REG_RST: u32 = 1 << 11; // Bluetooth MAC Regsiters
            const BTBB_REG_RST: u32 = 1 << 13; // Bluetooth Baseband Registers

            const MODEM_RESET_FIELD_WHEN_PU: u32 = WIFIBB_RST
                | FE_RST
                | WIFIMAC_RST
                | if cfg!(soc_has_bt) {
                    BTBB_RST | BTMAC_RST | RW_BTMAC_RST | RW_BTMAC_REG_RST | BTBB_REG_RST
                } else {
                    0
                };

            // FIXME: Hardcode the wifi clk register for now, need to find a better way to manage these "magic" registers
            let tmp = core::ptr::read_volatile(0x6002_6018 as *const u32);
            core::ptr::write_volatile(0x6002_6018 as *mut u32, tmp | MODEM_RESET_FIELD_WHEN_PU);
            let tmp = core::ptr::read_volatile(0x6002_6018 as *const u32);
            core::ptr::write_volatile(0x6002_6018 as *mut u32, tmp & !MODEM_RESET_FIELD_WHEN_PU);
        }

        self.inner
            .dig_iso
            .modify(RTC_CNTL_DIG_ISO::RTC_CNTL_WIFI_FORCE_ISO::CLEAR);
    }
}
