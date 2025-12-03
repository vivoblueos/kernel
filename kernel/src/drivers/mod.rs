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

use crate::devices::bus::BusInterface;

pub(crate) mod ic;
mod sensor;

/// use c-compatible error type
pub type Result<T> = core::result::Result<T, crate::error::Error>;

pub trait InitDriver<B: BusInterface>: Sized + Default {
    type Driver;
    fn init(self, bus: &mut B) -> Result<Self::Driver>;
}

pub trait DriverModule<B: BusInterface, D> {
    type Data: InitDriver<B, Driver = D>;
    fn probe(dev: &super::devices::DeviceData) -> Result<Self::Data>;
}
