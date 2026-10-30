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

use blueos_hal::pinctrl::AlterFuncPin;

pub enum GpioMode {
    Input(InputPullMode),
    AlterFunc(OutputType, OutputSpeed),
}

pub enum OutputType {
    PushPull,
    OpenDrain,
}

pub enum InputPullMode {
    None,
    PullUp,
    PullDown,
}

#[derive(PartialEq)]
pub enum OutputSpeed {
    Low,
    Medium,
    Fast,
    Max,
}

pub struct Gd32AlterfuncIO {
    base_addr: u32,
    pin: u32,
    mode: GpioMode,
}

impl Gd32AlterfuncIO {
    pub const fn new(base_addr: u32, pin: u32, mode: GpioMode) -> Self {
        Gd32AlterfuncIO {
            base_addr,
            pin,
            mode,
        }
    }
}

impl AlterFuncPin for Gd32AlterfuncIO {
    fn init(&self) {
        let ctl_addr = if self.pin < 8 {
            self.base_addr + 0x00
        } else {
            self.base_addr + 0x04
        };

        let mut bits = unsafe { core::ptr::read_volatile(ctl_addr as *const u32) };

        let shift = (self.pin % 8) * 4;
        bits &= !(0b0011 << shift); // Clear MODE bits

        unsafe {
            match self.mode {
                GpioMode::Input(ref pull_mode) => {
                    bits |= 0b00 << shift;
                    match pull_mode {
                        InputPullMode::None => {
                            bits &= !(0b1100 << shift); // Clear the CNF bits
                            bits |= 0b0100 << shift; // Set to Floating
                            unsafe { core::ptr::write_volatile(ctl_addr as *mut u32, bits) };
                        }
                        InputPullMode::PullUp => {
                            bits &= !(0b1100 << shift); // Clear the CNF bits
                            bits |= 0b1000 << shift; // Set to Pull-Up
                            unsafe { core::ptr::write_volatile(ctl_addr as *mut u32, bits) };
                            let bop = self.base_addr + 0x00000010;
                            unsafe { core::ptr::write_volatile(bop as *mut u32, 1 << self.pin) };
                        }
                        InputPullMode::PullDown => {
                            bits &= !(0b1100 << shift); // Clear the CNF bits
                            bits |= 0b1000 << shift; // Set to Pull-Down
                            core::ptr::write_volatile(ctl_addr as *mut u32, bits);
                            let bc = self.base_addr + 0x00000014;
                            core::ptr::write_volatile(bc as *mut u32, 1 << self.pin);
                        }
                    }
                }
                GpioMode::AlterFunc(ref output_type, ref speed) => {
                    match output_type {
                        OutputType::PushPull => {
                            bits &= !(0b1100 << shift); // Clear the CNF bits
                            bits |= 0b1100 << shift; // Set to AFIO Open-Drain
                        }
                        OutputType::OpenDrain => {
                            bits &= !(0b1100 << shift); // Clear the CNF bits
                            bits |= 0b1000 << shift; // Set to AFIO Push-Pull
                        }
                    }
                    match speed {
                        OutputSpeed::Low => bits |= 0b0001 << shift,
                        OutputSpeed::Medium => bits |= 0b0010 << shift,
                        OutputSpeed::Fast | OutputSpeed::Max => bits |= 0b0011 << shift,
                    }
                    unsafe { core::ptr::write_volatile(ctl_addr as *mut u32, bits) };

                    if speed == &OutputSpeed::Max {
                        let spd = self.base_addr + 0x3c;
                        let temp = core::ptr::read_volatile(spd as *const u32);
                        core::ptr::write_volatile(spd as *mut u32, temp | (1 << self.pin));
                    } else {
                        let spd = self.base_addr + 0x3c;
                        let temp = core::ptr::read_volatile(spd as *const u32);
                        core::ptr::write_volatile(spd as *mut u32, temp & !(1 << self.pin));
                    }
                }
            }
        }
    }
}
