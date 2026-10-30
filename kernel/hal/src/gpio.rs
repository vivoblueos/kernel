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

/// GPIO output pin — drives a GPIO output latch.
///
/// Uses `&self` (shared reference): the multitasking kernel shares peripheral
/// references across contexts, and mutual exclusion is provided at a higher
/// level (e.g. `embedded_hal_bus::spi::ExclusiveDevice` guards CS transitions).
pub trait OutputPin: super::PlatPeri {
    /// Drive the pin low.
    fn set_low(&self) -> super::err::Result<()>;

    /// Drive the pin high.
    fn set_high(&self) -> super::err::Result<()>;
}
