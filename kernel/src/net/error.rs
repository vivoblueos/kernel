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

//! Unified network error hierarchy for BlueOS.
//!
//! This module defines the error types used across all four network layers:
//! L2 (Link), L3 (NetIface), L4 (Protocol), and control path.

use alloc::string::String;
use thiserror::Error;

/// Unified network error covering all layers.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum NetError {
    // ── L2: Link layer errors ──
    #[error("Device not found: {0}")]
    DeviceNotFound(String),

    #[error("L2 send error: {0}")]
    L2SendError(String),

    #[error("L2 receive error: {0}")]
    L2RecvError(String),

    // ── L3: Network interface errors ──
    #[error("Interface not initialized: {0}")]
    InterfaceNotInitialized(String),

    #[error("No route to host")]
    NoRoute,

    #[error("Route error: {0}")]
    RouteError(String),

    #[error("IP address conflict")]
    IpAddrConflict,

    // ── L4: Protocol/transport errors ──
    #[error("Protocol already registered: {0}")]
    ProtocolAlreadyRegistered(u8),

    #[error("Protocol not registered: {0}")]
    ProtocolNotRegistered(u8),

    #[error("Operation timed out")]
    Timeout,

    #[error("Operation would block")]
    WouldBlock,

    // ── Socket errors ──
    #[error("Invalid socket fd: {0}")]
    InvalidSocketFd(i32),

    #[error("Invalid state: {0}")]
    InvalidState(String),

    #[error("Unsupported socket type")]
    UnsupportedSocketType,

    // ── Control path errors ──
    #[error("Control operation not supported: {0}")]
    ControlNotSupported(String),

    #[error("Device does not support this operation")]
    DeviceTraitNotAvailable,

    // ── IPC errors ──
    #[error("Network stack queue is full")]
    NetStackQueueFull,

    #[error("Lock failed: {0}")]
    LockFail(String),

    // ── General ──
    #[error("Not supported: {0}")]
    NotSupported(String),

    #[error("Invalid parameter: {0}")]
    InvalidParam(String),
}
