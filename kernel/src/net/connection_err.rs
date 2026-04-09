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

//! socket_err.rs
//! socket errors

use alloc::string::String;
use thiserror::Error;

use crate::{
    error::Error,
    net::{socket::socket_err::SocketError, SocketType},
};

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum ConnectionError {
    #[error("Connection timeout : {0}")]
    Timeout(usize),

    #[error("Network stack queue is full")]
    NetStackQueueFull,

    #[error("Lock fail {0}")]
    LockFail(String),

    #[error("Unsupported socket type {0}")]
    UnsupportedSocketType(SocketType),

    #[error("All dynamic ports are in use")]
    NoAvailableDynamicPort,

    #[error("Port {0} is already in use")]
    PortInUse(u16),

    #[error("Port {0} is invalid : {1}")]
    PortOutOfRange(u16, String),

    #[error("Posix error : {0}")]
    PosixError(Error),

    #[error("Socket operation error : {0}")]
    SocketOperationError(SocketError),
}

impl From<SocketError> for ConnectionError {
    fn from(err: SocketError) -> Self {
        Self::SocketOperationError(err)
    }
}

impl From<Error> for ConnectionError {
    fn from(err: Error) -> Self {
        Self::PosixError(err)
    }
}
