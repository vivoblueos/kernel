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

//! Device operation errors in BlueOS Kernel

#![no_std]

/// Errors that can occur during HAL operations.
#[non_exhaustive]
#[derive(Debug, Clone, Eq, PartialEq)]
#[cfg_attr(feature = "thiserror", derive(thiserror::Error))]
pub enum HalError<T = &'static str> {
    /// Operation can not be continued.
    Fail,
    /// Device is busy. Try again later.
    Busy,
    /// Device is not ready. Please initialize it first.
    NotReady,
    /// Invalid parameter.
    InvalidParam,
    /// Operation is not supported. Please check the API.
    NotSupport,
    /// Operation timed out.
    Timeout,
    /// No memory.
    NoMemory,
    /// No acknowledgment received.
    NoAck,
    /// No data available.
    NoData,
    /// I/O error.
    IoError,
    /// Other errors.
    Other(T),
}

pub type Result<T> = core::result::Result<T, HalError>;

impl embedded_hal::i2c::Error for HalError {
    fn kind(&self) -> embedded_hal::i2c::ErrorKind {
        match self {
            Self::IoError => embedded_hal::i2c::ErrorKind::Bus,
            Self::Timeout => embedded_hal::i2c::ErrorKind::ArbitrationLoss,
            Self::NoAck => embedded_hal::i2c::ErrorKind::NoAcknowledge(
                embedded_hal::i2c::NoAcknowledgeSource::Unknown,
            ),
            _ => embedded_hal::i2c::ErrorKind::Other,
        }
    }
}
