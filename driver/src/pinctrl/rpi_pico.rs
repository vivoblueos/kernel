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

use crate::static_ref::StaticRef;
use blueos_hal::pinctrl::AlterFuncPin;
use tock_registers::{
    interfaces::{ReadWriteable, Writeable},
    register_bitfields, register_structs,
    registers::{ReadOnly, ReadWrite},
};

#[repr(C)]
struct GpioPinReg {
    status: ReadOnly<u32, GPIOx_STATUS::Register>,
    ctrl: ReadWrite<u32, GPIOx_CTRL::Register>,
}

register_structs! {
    /// GPIO Registers.
    GpioRegisters {
        (0x000 => pin: [GpioPinReg; 48]),

        /// End
        (0x180 => @END),
    },
    /// User Bank Pad Control Registers
    GpioPadRegisters {
        /// Voltage select
        (0x00 => voltage: ReadWrite<u32, VOLTAGE_SELECT::Register>),

        /// Pads control
        (0x04 => gpio_pad: [ReadWrite<u32, GPIO_PAD::Register>; 48]),

        /// End
        (0xc4 => @END),
    }
}

register_bitfields! [u32,
    GPIOx_STATUS [
        /// interrupt to processors, after override is applied
        IRQTOPROC OFFSET(26) NUMBITS(1) [],
        /// input signal from pad, before override is applied
        INFROMPAD OFFSET(17) NUMBITS(1) [],
        /// output enable to pad after register override is applied
        OETOPAD OFFSET(13) NUMBITS(1) [],
        /// output signal to pad after register override is applied
        OUTTOPAD OFFSET(9) NUMBITS(1) [],
    ],
    GPIOx_CTRL [
        /// interrupt override?
        IRQOVER OFFSET(28) NUMBITS(2) [
            NoInvert = 0,
            Invert = 1,
            DriveLow = 2,
            DriveHigh = 3
        ],
        /// input override
        INOVER OFFSET(16) NUMBITS(2) [
            NoInvert = 0,
            Invert = 1,
            DriveLow = 2,
            DriveHigh = 3
        ],
        /// output enable override
        OEOVER OFFSET(14) NUMBITS(2) [
            EnableSignal = 0,
            EnableInverseSignal = 1,
            Disable = 2,
            Enable = 3
        ],
        /// output override
        OUTOVER OFFSET(12) NUMBITS(2) [
            Signal = 0,
            InverseSignal = 1,
            Low = 2,
            High = 3
        ],
        /// Function select
        FUNCSEL OFFSET(0) NUMBITS(5) []
    ],
    VOLTAGE_SELECT[
        VOLTAGE OFFSET(0) NUMBITS(1) [
            Set3V3 = 0,
            Set1V8 = 1
        ]
    ],
    GPIO_PAD [
        ISO OFFSET(8) NUMBITS(1) [],
        OD OFFSET(7) NUMBITS(1) [],
        IE OFFSET(6) NUMBITS(1) [],
        DRIVE OFFSET(4) NUMBITS(2) [],
        PUE OFFSET(3) NUMBITS(1) [],
        PDE OFFSET(2) NUMBITS(1) [],
        SCHMITT OFFSET(1) NUMBITS(1) [],
        SLEWFAST OFFSET(0) NUMBITS(1) []
    ],
];

const GPIO_BASE_ADDRESS: usize = 0x40028000;
const GPIO_BASE: StaticRef<GpioRegisters> =
    unsafe { StaticRef::new(GPIO_BASE_ADDRESS as *const GpioRegisters) };

const GPIO_PAD_BASE_ADDRESS: usize = 0x40038000;
const GPIO_PAD_BASE: StaticRef<GpioPadRegisters> =
    unsafe { StaticRef::new(GPIO_PAD_BASE_ADDRESS as *const GpioPadRegisters) };

pub struct RpiPicoPinctrl {
    pin: u32,
    function: u32,
}

impl RpiPicoPinctrl {
    pub const fn new(pin: u32, function: u32) -> Self {
        RpiPicoPinctrl { pin, function }
    }

    fn activate_pads(&self) {
        GPIO_PAD_BASE.gpio_pad[self.pin as usize].modify(GPIO_PAD::OD::CLEAR + GPIO_PAD::IE::SET);
    }

    fn ctrl_iso(&self, iso: u32) {
        GPIO_PAD_BASE.gpio_pad[self.pin as usize].modify(GPIO_PAD::ISO.val(iso));
    }
}

impl AlterFuncPin for RpiPicoPinctrl {
    fn init(&self) {
        self.activate_pads();
        let func = self.function;
        self.ctrl_iso(0);
        GPIO_BASE.pin[self.pin as usize].ctrl.set(0);
        GPIO_BASE.pin[self.pin as usize]
            .ctrl
            .modify(GPIOx_CTRL::FUNCSEL.val(func as u32));
    }
}
