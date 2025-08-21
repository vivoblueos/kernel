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

// SPDX-License-Identifier: MIT OR Apache-2.0

#[cfg(target_arch = "arm")]
pub(crate) mod cmsdk_uart;

#[cfg(target_arch = "riscv64")]
pub(crate) mod ns16550a;

#[cfg(target_arch = "aarch64")]
pub(crate) mod arm_pl011;

use crate::devices::tty::serial::UartOps;
use embedded_io::{Read, ReadReady, Write, WriteReady};
