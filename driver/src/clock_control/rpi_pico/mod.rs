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

mod clocks;
mod pll;
mod reset;
mod xosc;
use crate::clock_control::{
    rpi_pico as rp235x,
    rpi_pico::{
        clocks::{
            PeripheralAuxiliaryClockSource, ReferenceAuxiliaryClockSource, ReferenceClockSource,
            SystemAuxiliaryClockSource, SystemClockSource,
        },
        pll::PLLConfig,
        reset::{Peripheral, Resets},
    },
};
use blueos_hal::clock_control::ClockControl;

pub struct RpiPicoClockControl;

pub const PLL_SYS_150MHZ: PLLConfig = PLLConfig {
    fbdiv: 125,
    refdiv: 1,
    postdiv1: 5,
    postdiv2: 2,
};

pub const PLL_USB_48MHZ: PLLConfig = PLLConfig {
    fbdiv: 100,
    refdiv: 1,
    postdiv1: 5,
    postdiv2: 5,
};

impl ClockControl for RpiPicoClockControl {
    fn init() {
        let _ = rp235x::xosc::start_xosc(12_000_000);

        rp235x::clocks::disable_clk_sys_resus();
        rp235x::clocks::disable_sys_aux();
        rp235x::clocks::disable_ref_aux();

        let reset = Resets::new();

        reset.reset_all_except(&[
            Peripheral::IOQSpi,
            Peripheral::PadsBank0,
            Peripheral::PllUsb,
            Peripheral::PllUsb,
        ]);

        reset.unreset_all_except(
            &[
                Peripheral::Adc,
                Peripheral::Sha256,
                Peripheral::HSTX,
                Peripheral::Spi0,
                Peripheral::Spi1,
                Peripheral::I2c0,
                Peripheral::I2c1,
                Peripheral::Uart0,
                Peripheral::Uart1,
                Peripheral::UsbCtrl,
            ],
            true,
        );

        reset.reset(&[Peripheral::PllSys, Peripheral::PllUsb]);
        reset.unreset(&[Peripheral::PllSys, Peripheral::PllUsb], true);

        let pll_sys_freq =
            rp235x::pll::configure_pll(rp235x::pll::PLL::Sys, 12_000_000, &PLL_SYS_150MHZ);
        let pll_usb_freq =
            rp235x::pll::configure_pll(rp235x::pll::PLL::Usb, 12_000_000, &PLL_USB_48MHZ);

        rp235x::clocks::configure_reference_clock(
            ReferenceClockSource::Xosc,
            ReferenceAuxiliaryClockSource::PllUsb,
            1,
        );

        rp235x::clocks::configure_system_clock(
            SystemClockSource::Auxiliary,
            SystemAuxiliaryClockSource::PllSys,
            1,
            0,
        );

        rp235x::clocks::configure_peripheral_clock(PeripheralAuxiliaryClockSource::PllSys);
    }
}
