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

// ESP32-C3 GPIO + IO_MUX + GPIO Matrix driver
//
// Reference: ESP32-C3 Technical Reference Manual, Chapter 4 (IO_MUX/GPIO)
// Reference: ESP-IDF soc/esp32c3/include/soc/gpio_reg.h, io_mux_reg.h, gpio_sig_map.h
//
// ESP32-C3 SPI2 (FSPI) signals are routed through the GPIO Matrix,
// not through IO_MUX FUNC selection. This driver configures both:
// - IO_MUX: per-pin pull-up/pull-down, input enable, MCU_SEL (function select)
// - GPIO Matrix: maps peripheral output signals to GPIO pins
// - GPIO output: direct pin output control for CS (software-controlled)

use crate::static_ref::StaticRef;
use blueos_hal::pinctrl::AlterFuncPin;
use embedded_hal::digital::OutputPin;
use tock_registers::{
    interfaces::Writeable, register_bitfields, register_structs, registers::ReadWrite,
};

// ─── Base addresses ──────────────────────────────────────────────────────

// GPIO controller (output/enable/matrix)
const GPIO_BASE: StaticRef<GpioRegisters> =
    unsafe { StaticRef::new(0x60004000 as *const GpioRegisters) };

// ─── GPIO Matrix signal indices (from gpio_sig_map.h) ────────────────────
// These map SPI2/FSPI peripheral signals to GPIO pins via the GPIO Matrix.

/// FSPICLK — SPI2 clock output signal
const FSPICLK_OUT_IDX: u32 = 63;
/// FSPIQ — SPI2 MISO (data in) signal
const FSPIQ_IN_IDX: u32 = 64;
/// FSPID — SPI2 MOSI (data out) signal
const FSPID_OUT_IDX: u32 = 65;
/// FSPICS0 — SPI2 chip select 0 output signal
const FSPICS0_OUT_IDX: u32 = 68;

// ─── IO_MUX per-pin register offsets ─────────────────────────────────────
// IO_MUX registers are NOT at contiguous 4*GPIO offsets.
// Each GPIO has a named register at a specific offset (from io_mux_reg.h).

/// IO_MUX register offset for each GPIO (0-21), relative to IO_MUX base (0x60009000).
/// Index = GPIO number. Value = offset in bytes.
const IO_MUX_OFFSETS: [u32; 22] = [
    0x04, // GPIO0  — PERIPHS_IO_MUX_XTAL_32K_P_U
    0x08, // GPIO1  — PERIPHS_IO_MUX_XTAL_32K_N_U
    0x0C, // GPIO2  — PERIPHS_IO_MUX_GPIO2_U
    0x10, // GPIO3  — PERIPHS_IO_MUX_GPIO3_U
    0x14, // GPIO4  — PERIPHS_IO_MUX_MTMS_U
    0x18, // GPIO5  — PERIPHS_IO_MUX_MTDI_U
    0x1C, // GPIO6  — PERIPHS_IO_MUX_MTCK_U
    0x20, // GPIO7  — PERIPHS_IO_MUX_MTDO_U
    0x24, // GPIO8  — PERIPHS_IO_MUX_GPIO8_U
    0x28, // GPIO9  — PERIPHS_IO_MUX_GPIO9_U
    0x2C, // GPIO10 — PERIPHS_IO_MUX_GPIO10_U
    0x30, // GPIO11 — PERIPHS_IO_MUX_VDD_SPI_U
    0x34, // GPIO12 — PERIPHS_IO_MUX_SPIHD_U
    0x38, // GPIO13 — PERIPHS_IO_MUX_SPIWP_U
    0x3C, // GPIO14 — PERIPHS_IO_MUX_SPICS0_U
    0x40, // GPIO15 — PERIPHS_IO_MUX_SPICLK_U
    0x44, // GPIO16 — PERIPHS_IO_MUX_SPID_U
    0x48, // GPIO17 — PERIPHS_IO_MUX_SPIQ_U
    0x4C, // GPIO18 — PERIPHS_IO_MUX_GPIO18_U
    0x50, // GPIO19 — PERIPHS_IO_MUX_GPIO19_U
    0x54, // GPIO20 — PERIPHS_IO_MUX_U0RXD_U
    0x58, // GPIO21 — PERIPHS_IO_MUX_U0TXD_U
];

const IO_MUX_BASE: usize = 0x60009000;

// ─── IO_MUX register bit fields (from io_mux_reg.h) ─────────────────────
// MCU_SEL at bits 12-14 (3 bits, values 0-7)
// FUN_IE   at bit 9 (input enable)
// FUN_DRV  at bits 10-11 (drive strength, 0-3)
// FUN_PU   at bit 8 (pull-up)
// FUN_PD   at bit 7 (pull-down)

register_bitfields! [
    u32,

    pub IoMuxFields [
        MCU_SEL OFFSET(12) NUMBITS(3) [
            Func0 = 0,  // Default (JTAG/special)
            Func1 = 1,  // GPIO function (PIN_FUNC_GPIO)
            Func2 = 2,  // FSPI (SPI2) function for some pins
        ],
        FUN_DRV OFFSET(10) NUMBITS(2) [
            Drive0 = 0,  // Weakest
            Drive1 = 1,
            Drive2 = 2,
            Drive3 = 3,  // Strongest
        ],
        FUN_IE  OFFSET(9)  NUMBITS(1) [],  // Input enable
        FUN_PU  OFFSET(8)  NUMBITS(1) [],  // Pull-up
        FUN_PD  OFFSET(7)  NUMBITS(1) [],  // Pull-down
    ],
];

register_bitfields! [
    u32,

    pub GpioOut [
        DATA OFFSET(0) NUMBITS(26) [],
    ],
    pub GpioEnable [
        DATA OFFSET(0) NUMBITS(26) [],
    ],
];

// ─── GPIO controller registers ──────────────────────────────────────────

register_structs! {
    GpioRegisters {
        (0x000 => bt_select: ReadWrite<u32>),
        (0x004 => out: ReadWrite<u32, GpioOut::Register>),
        (0x008 => out_w1ts: ReadWrite<u32, GpioOut::Register>),
        (0x00C => out_w1tc: ReadWrite<u32, GpioOut::Register>),
        (0x010 => _reserved0),
        (0x020 => enable: ReadWrite<u32, GpioEnable::Register>),
        (0x024 => enable_w1ts: ReadWrite<u32, GpioEnable::Register>),
        (0x028 => enable_w1tc: ReadWrite<u32, GpioEnable::Register>),
        (0x02C => @END),
    }
}

// ─── GPIO Matrix output function selection (from gpio_reg.h) ─────────────
// GPIO_FUNCx_OUT_SEL_CFG_REG at offset 0x554 + 4*x
// Each register has:
//   OUT_SEL: bits 0-7 — which peripheral signal index to route to GPIO x
//   INV_SEL: bit 8    — invert the output signal
//   OEN_SEL: bit 9    — 0=peripheral controls output enable, 1=GPIO register controls
//   OEN_INV_SEL: bit 10 — invert output enable signal
//
// For SPI2 output pins (CLK, MOSI, CS), we route the FSPI signal.
// For CS pin (software-controlled), we set OEN_SEL=1 (GPIO controls enable).

register_bitfields! [
    u32,

    pub FuncOutSelCfg [
        OUT_SEL     OFFSET(0)  NUMBITS(8) [],   // Peripheral signal index
        INV_SEL     OFFSET(8)  NUMBITS(1) [],   // Invert output
        OEN_SEL     OFFSET(9)  NUMBITS(1) [
            Peripheral = 0,  // Peripheral controls output enable
            GpioReg     = 1,  // GPIO_ENABLE_REG controls output enable
        ],
        OEN_INV_SEL OFFSET(10) NUMBITS(1) [],   // Invert output enable
    ],
];

// ─── GPIO Matrix input function selection (from gpio_reg.h) ──────────────
// GPIO_FUNCx_IN_SEL_CFG_REG at offset 0x154 + 4*x
// Each register has:
//   IN_SEL: bits 0-4 — which GPIO pin to route to this peripheral input signal
//   IN_INV_SEL: bit 5 — invert input

register_bitfields! [
    u32,

    pub FuncInSelCfg [
        IN_SEL     OFFSET(0) NUMBITS(5) [],   // GPIO pin number for input
        IN_INV_SEL OFFSET(5) NUMBITS(1) [],   // Invert input
        SEL        OFFSET(6) NUMBITS(1) [],   // 1 = route via GPIO Matrix (do not bypass), 0 = bypass
    ],
];

// ─── Helper: write IO_MUX register for a GPIO pin ────────────────────────

fn write_io_mux(pin: u8, mcu_sel: u32, ie: bool, pu: bool, pd: bool, drv: u32) {
    let offset = IO_MUX_OFFSETS[pin as usize];
    let addr = IO_MUX_BASE + offset as usize;
    let reg = unsafe { &*(addr as *const ReadWrite<u32, IoMuxFields::Register>) };
    reg.write(
        IoMuxFields::MCU_SEL.val(mcu_sel)
            + IoMuxFields::FUN_IE.val(if ie { 1 } else { 0 })
            + IoMuxFields::FUN_PU.val(if pu { 1 } else { 0 })
            + IoMuxFields::FUN_PD.val(if pd { 1 } else { 0 })
            + IoMuxFields::FUN_DRV.val(drv),
    );
}

// ─── Helper: route peripheral output signal to a GPIO pin ────────────────
// Writes GPIO_FUNCx_OUT_SEL_CFG_REG to connect signal_idx to GPIO pin.

fn route_signal_out(pin: u8, signal_idx: u32, oen_sel: u32) {
    let offset = 0x554 + 4 * pin as usize;
    let addr = 0x60004000 + offset;
    let reg = unsafe { &*(addr as *const ReadWrite<u32, FuncOutSelCfg::Register>) };
    reg.write(
        FuncOutSelCfg::OUT_SEL.val(signal_idx)
            + FuncOutSelCfg::INV_SEL.val(0)
            + FuncOutSelCfg::OEN_SEL.val(oen_sel)
            + FuncOutSelCfg::OEN_INV_SEL.val(0),
    );
}

// ─── Helper: route GPIO pin to peripheral input signal ───────────────────
// Writes GPIO_FUNCx_IN_SEL_CFG_REG to connect GPIO pin to signal_idx.

fn route_signal_in(signal_idx: u32, pin: u32) {
    let offset = 0x154 + 4 * signal_idx as usize;
    let addr = 0x60004000 + offset;
    let reg = unsafe { &*(addr as *const ReadWrite<u32, FuncInSelCfg::Register>) };
    reg.write(
        FuncInSelCfg::SEL.val(1) + FuncInSelCfg::IN_INV_SEL.val(0) + FuncInSelCfg::IN_SEL.val(pin),
    );
}

// ─── Esp32IoMuxPinctrl — PinMux configuration for define_pin_states! ────

/// ESP32-C3 PinMux configuration entry
///
/// Combines IO_MUX, GPIO Matrix, and GPIO output enable configuration.
/// Used with `define_pin_states!` macro to configure SPI2 pins.
///
/// SPI2 (FSPI) signals on ESP32-C3 are routed through the GPIO Matrix,
/// not via IO_MUX FUNC selection. MCU_SEL=1 (GPIO function) is required
/// so the GPIO Matrix can take over signal routing.
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
        // 1. Configure IO_MUX: function select, pull-up/down, input enable, drive
        write_io_mux(self.pin, self.mcu_sel, self.ie, self.pu, self.pd, self.drv);

        // 2. Route peripheral output signal to this GPIO pin via GPIO Matrix
        if let Some(signal_idx) = self.out_signal {
            if self.gpio_output {
                // Software-controlled pin (e.g., CS): OEN_SEL=1 (GPIO_ENABLE controls)
                route_signal_out(self.pin, signal_idx, 1u32);
            } else {
                // Peripheral-controlled pin (CLK, MOSI): OEN_SEL=0 (peripheral controls)
                route_signal_out(self.pin, signal_idx, 0u32);
            }
        }

        // 3. Route this GPIO pin to peripheral input signal via GPIO Matrix
        if let Some(signal_idx) = self.in_signal {
            route_signal_in(signal_idx, self.pin as u32);
        }

        // 4. Enable GPIO output for software-controlled pins (CS).
        // Order matters: pre-set the output latch HIGH *before* enabling output,
        // so the pin is driven high the instant output turns on — no low glitch
        // on CS during the enable moment.
        if self.gpio_output {
            let gpio_regs = &*GPIO_BASE;
            gpio_regs.out_w1ts.write(GpioOut::DATA.val(1 << self.pin));
            gpio_regs
                .enable_w1ts
                .write(GpioEnable::DATA.val(1 << self.pin));
        }
    }
}

// ─── Esp32GpioOutputPin — OutputPin for ExclusiveDevice CS control ──────

/// GPIO output pin for ESP32-C3
///
/// Implements `embedded_hal::digital::OutputPin` for use as CS pin
/// with `embedded_hal_bus::spi::ExclusiveDevice`.
///
/// Uses atomic W1TS/W1TC registers for glitch-free set_low/set_high.
pub struct Esp32GpioOutputPin<const PIN: u8>;

impl<const PIN: u8> Esp32GpioOutputPin<PIN> {
    pub const fn new() -> Self {
        Esp32GpioOutputPin
    }
}

impl<const PIN: u8> embedded_hal::digital::ErrorType for Esp32GpioOutputPin<PIN> {
    type Error = core::convert::Infallible;
}

impl<const PIN: u8> OutputPin for Esp32GpioOutputPin<PIN> {
    fn set_low(&mut self) -> Result<(), Self::Error> {
        // Assert CS (active-low) — drive pin LOW
        let gpio_regs = &*GPIO_BASE;
        gpio_regs.out_w1tc.write(GpioOut::DATA.val(1 << PIN));
        Ok(())
    }

    fn set_high(&mut self) -> Result<(), Self::Error> {
        // Deassert CS — drive pin HIGH
        let gpio_regs = &*GPIO_BASE;
        gpio_regs.out_w1ts.write(GpioOut::DATA.val(1 << PIN));
        Ok(())
    }
}
