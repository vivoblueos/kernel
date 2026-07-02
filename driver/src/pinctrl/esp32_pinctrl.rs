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

//! ESP32-C3 IO_MUX + GPIO Matrix pin controller.

use crate::{
    gpio::esp32_gpio::{GpioEnable, GpioOut, GpioRegisters, GPIO_BASE},
    static_ref::StaticRef,
};
use blueos_hal::pinctrl::AlterFuncPin;
use tock_registers::{interfaces::Writeable, register_bitfields, registers::ReadWrite};

// SPI2/FSPI signal indices routed through the GPIO Matrix (gpio_sig_map.h).
const FSPICLK_OUT_IDX: u32 = 63;
const FSPIQ_IN_IDX: u32 = 64;
const FSPID_OUT_IDX: u32 = 65;
const FSPICS0_OUT_IDX: u32 = 68;

// IO_MUX per-pin register offsets relative to IO_MUX base (0x60009000).
const IO_MUX_OFFSETS: [u32; 22] = [
    0x04, // GPIO0
    0x08, // GPIO1
    0x0C, // GPIO2
    0x10, // GPIO3
    0x14, // GPIO4
    0x18, // GPIO5
    0x1C, // GPIO6
    0x20, // GPIO7
    0x24, // GPIO8
    0x28, // GPIO9
    0x2C, // GPIO10
    0x30, // GPIO11
    0x34, // GPIO12
    0x38, // GPIO13
    0x3C, // GPIO14
    0x40, // GPIO15
    0x44, // GPIO16
    0x48, // GPIO17
    0x4C, // GPIO18
    0x50, // GPIO19
    0x54, // GPIO20
    0x58, // GPIO21
];

const IO_MUX_BASE: usize = 0x60009000;

register_bitfields! [
    u32,

    pub IoMuxFields [
        MCU_SEL OFFSET(12) NUMBITS(3) [
            Func0 = 0,  // Default (JTAG/special)
            Func1 = 1,  // GPIO function
            Func2 = 2,  // FSPI (SPI2) function for some pins
        ],
        FUN_DRV OFFSET(10) NUMBITS(2) [
            Drive0 = 0,
            Drive1 = 1,
            Drive2 = 2,
            Drive3 = 3,
        ],
        FUN_IE  OFFSET(9)  NUMBITS(1) [],  // Input enable
        FUN_PU  OFFSET(8)  NUMBITS(1) [],  // Pull-up
        FUN_PD  OFFSET(7)  NUMBITS(1) [],  // Pull-down
    ],
];

register_bitfields! [
    u32,

    // GPIO_FUNCx_OUT_SEL_CFG_REG: route a peripheral output signal to GPIO x.
    pub FuncOutSelCfg [
        OUT_SEL     OFFSET(0)  NUMBITS(8) [],
        INV_SEL     OFFSET(8)  NUMBITS(1) [],
        OEN_SEL     OFFSET(9)  NUMBITS(1) [
            Peripheral = 0,  // Peripheral controls output enable
            GpioReg     = 1,  // GPIO_ENABLE_REG controls output enable
        ],
        OEN_INV_SEL OFFSET(10) NUMBITS(1) [],
    ],
];

register_bitfields! [
    u32,

    // GPIO_FUNCx_IN_SEL_CFG_REG: route GPIO pin to a peripheral input signal.
    pub FuncInSelCfg [
        IN_SEL     OFFSET(0) NUMBITS(5) [],
        IN_INV_SEL OFFSET(5) NUMBITS(1) [],
        SEL        OFFSET(6) NUMBITS(1) [],  // 1 = route via GPIO Matrix, 0 = bypass
    ],
];

fn write_io_mux(pin: u8, mcu_sel: u32, ie: bool, pu: bool, pd: bool, drv: u32) {
    let addr = IO_MUX_BASE + IO_MUX_OFFSETS[pin as usize] as usize;
    let reg = unsafe { &*(addr as *const ReadWrite<u32, IoMuxFields::Register>) };
    reg.write(
        IoMuxFields::MCU_SEL.val(mcu_sel)
            + IoMuxFields::FUN_IE.val(if ie { 1 } else { 0 })
            + IoMuxFields::FUN_PU.val(if pu { 1 } else { 0 })
            + IoMuxFields::FUN_PD.val(if pd { 1 } else { 0 })
            + IoMuxFields::FUN_DRV.val(drv),
    );
}

fn route_signal_out(pin: u8, signal_idx: u32, oen_sel: u32) {
    let addr = 0x60004000 + 0x554 + 4 * pin as usize;
    let reg = unsafe { &*(addr as *const ReadWrite<u32, FuncOutSelCfg::Register>) };
    reg.write(
        FuncOutSelCfg::OUT_SEL.val(signal_idx)
            + FuncOutSelCfg::INV_SEL.val(0)
            + FuncOutSelCfg::OEN_SEL.val(oen_sel)
            + FuncOutSelCfg::OEN_INV_SEL.val(0),
    );
}

fn route_signal_in(signal_idx: u32, pin: u32) {
    let addr = 0x60004000 + 0x154 + 4 * signal_idx as usize;
    let reg = unsafe { &*(addr as *const ReadWrite<u32, FuncInSelCfg::Register>) };
    reg.write(
        FuncInSelCfg::SEL.val(1) + FuncInSelCfg::IN_INV_SEL.val(0) + FuncInSelCfg::IN_SEL.val(pin),
    );
}

/// PinMux configuration entry used with `define_pin_states!`.
pub struct Esp32IoMuxPinctrl {
    pin: u8,
    mcu_sel: u32,
    ie: bool,
    pu: bool,
    pd: bool,
    drv: u32,
    out_signal: Option<u32>,
    in_signal: Option<u32>,
    gpio_output: bool,
}

impl Esp32IoMuxPinctrl {
    pub const fn new(
        pin: u8,
        mcu_sel: u32,
        ie: bool,
        pu: bool,
        pd: bool,
        drv: u32,
        out_signal: Option<u32>,
        in_signal: Option<u32>,
        gpio_output: bool,
    ) -> Self {
        Esp32IoMuxPinctrl {
            pin,
            mcu_sel,
            ie,
            pu,
            pd,
            drv,
            out_signal,
            in_signal,
            gpio_output,
        }
    }
}

impl AlterFuncPin for Esp32IoMuxPinctrl {
    fn init(&self) {
        write_io_mux(self.pin, self.mcu_sel, self.ie, self.pu, self.pd, self.drv);

        if let Some(signal_idx) = self.out_signal {
            // Software-controlled pins (CS) use OEN_SEL=1; peripheral pins use OEN_SEL=0.
            let oen_sel = if self.gpio_output { 1u32 } else { 0u32 };
            route_signal_out(self.pin, signal_idx, oen_sel);
        }

        if let Some(signal_idx) = self.in_signal {
            route_signal_in(signal_idx, self.pin as u32);
        }

        // For software-controlled pins, pre-set output HIGH before enabling to
        // avoid a low glitch on CS at the enable moment.
        if self.gpio_output {
            let gpio_regs = &*GPIO_BASE;
            gpio_regs.out_w1ts.write(GpioOut::DATA.val(1 << self.pin));
            gpio_regs
                .enable_w1ts
                .write(GpioEnable::DATA.val(1 << self.pin));
        }
    }
}
