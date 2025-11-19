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

//! # GD32 AFIO (Alternate Function I/O) Pin Control Driver
//!
//! This module provides a Rust implementation of the GD32 AFIO pin control driver,
//! which manages pin multiplexing and configuration for GD32 microcontrollers
//! that use the AFIO (Alternate Function I/O) model.
//!
//! ## Overview
//!
//! The AFIO model is used by legacy GD32 series including:
//! - GD32VW55x series
//!

use blueos_hal::pinctrl::AlterFuncPin;

unsafe extern "C" {
    fn gpio_mode_set(reg: u32, mode: u32, pull_up_down: u32, pin: u32);
    fn gpio_output_options_set(reg: u32, otype: u8, speed: u32, pin: u32);
    fn gpio_af_set(reg: u32, alt_func_num: u32, pin: u32);
}

macro_rules! bit {
    ($x:expr) => {
        (1u32 << $x)
    };
}

macro_rules! bits {
    ($start:expr, $end:expr) => {
        (0xFFFFFFFF << $start) & (0xFFFFFFFF >> (31 - $end))
    };
}

macro_rules! pud_pupd {
    ($regval:expr) => {
        bits!(0, 1) & ($regval as u32)
    };
}

macro_rules! af {
    ($val:expr) => {
        bits!(0, 3) & ($val as u32)
    };
}

macro_rules! ospd_ospd {
    ($regval:expr) => {
        bits!(0, 1) & ($regval as u32)
    };
}

#[derive(Clone, Copy)]
#[repr(u32)]
pub enum PullMode {
    None = pud_pupd!(0),
    PullUp = pud_pupd!(1),
    PullDown = pud_pupd!(2),
}

#[derive(Clone, Copy)]
#[repr(u32)]
pub enum AfioMode {
    Af0 = af!(0),
    Af1 = af!(1),
    Af2 = af!(2),
    Af3 = af!(3),
    Af4 = af!(4),
    Af5 = af!(5),
    Af6 = af!(6),
    Af7 = af!(7),
    Af8 = af!(8),
    Af9 = af!(9),
    Af10 = af!(10),
    Af11 = af!(11),
    Af12 = af!(12),
    Af13 = af!(13),
    Af14 = af!(14),
    Af15 = af!(15),
}

#[derive(Clone, Copy)]
#[repr(u32)]
pub enum OutputType {
    PushPull = 0,
    OpenDrain = 1,
}

#[derive(Clone, Copy)]
#[repr(u32)]
pub enum OutputSpeed {
    Low = ospd_ospd!(0),
    Medium = ospd_ospd!(1),
    Fast = ospd_ospd!(2),
    Max = ospd_ospd!(3),
}

pub struct Gd32Alterfunc {
    base_addr: u32,
    pin: u32,
    pull_mode: PullMode,
    afio_mode: AfioMode,
    output_type: OutputType,
    speed: OutputSpeed,
}

impl Gd32Alterfunc {
    pub const fn new(
        base_addr: u32,
        pin: u32,
        pull_mode: PullMode,
        afio_mode: AfioMode,
        output_type: OutputType,
        speed: OutputSpeed,
    ) -> Self {
        Gd32Alterfunc {
            base_addr,
            pin,
            pull_mode,
            afio_mode,
            output_type,
            speed,
        }
    }
}

impl AlterFuncPin for Gd32Alterfunc {
    fn init(&self) {
        unsafe {
            gpio_af_set(self.base_addr, self.afio_mode as u32, bit!(self.pin));

            gpio_mode_set(
                self.base_addr,
                0x0000_0002,
                self.pull_mode as u32,
                bit!(self.pin),
            );

            gpio_output_options_set(
                self.base_addr,
                self.output_type as u8,
                self.speed as u32,
                bit!(self.pin),
            );
        }
    }
}
