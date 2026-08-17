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

// SPDX-License-Identifier: MIT OR Apache-2.0

#[cfg(enable_block)]
pub mod spi_flash;
#[cfg(enable_block)]
pub mod spi_flash_cmd;

#[cfg(soc_esp32c3)]
mod esp32_rom;

#[cfg(soc_esp32c3)]
pub(crate) mod internal_flash;

#[cfg(soc_esp32c3)]
pub mod flash_mmap;

#[cfg(soc_esp32c3)]
pub(crate) mod esp32_flash;

#[cfg(soc_esp32c3)]
pub(crate) use esp32_flash::init_esp32_flash_device;

#[cfg(soc_esp32c3)]
pub(crate) use internal_flash::init_internal_flash;
