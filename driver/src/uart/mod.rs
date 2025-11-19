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

pub mod arm_pl011;
pub mod cmsdk;
pub mod dumb;
#[cfg(target_board = "gd32e507")]
pub mod gd32e5x_uart;
#[cfg(target_board = "gd32vw553")]
pub mod gd32vw55x;
pub mod ns16650;

#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(C)]
pub enum Parity {
    None = 0,
    Odd = 1,
    Even = 2,
    Mark = 3,
    Space = 4,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(C)]
pub enum StopBits {
    DataBits0_5 = 0,
    DataBits1 = 1,
    DataBits1_5 = 2,
    DataBits2 = 3,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(C)]
pub enum DataBits {
    DataBits5 = 0,
    DataBits6 = 1,
    DataBits7 = 2,
    DataBits8 = 3,
    DataBits9 = 4,
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[repr(C)]
pub enum FlowCtrl {
    // No flow control
    None = 0,
    // RTS/CTS
    RtsCts = 1,
    // DTR/DSR
    DtrDsr = 2,
    // RS485
    Rs485 = 3,
}

pub struct UartConfig {
    pub baudrate: u32,
    pub parity: Parity,
    pub stop_bits: StopBits,
    pub data_bits: DataBits,
    pub flow_ctrl: FlowCtrl,
}

impl Default for UartConfig {
    fn default() -> Self {
        UartConfig {
            baudrate: 115200,
            parity: Parity::None,
            stop_bits: StopBits::DataBits1,
            data_bits: DataBits::DataBits8,
            flow_ctrl: FlowCtrl::None,
        }
    }
}

#[non_exhaustive]
pub enum InterruptType {
    All,
    Rx,
    Tx,
    Unknown,
}

#[non_exhaustive]
pub enum UartCtrlStatus {
    OverrunError,
    BreakError,
    ParityError,
    FramingError,
    Normal,
}
