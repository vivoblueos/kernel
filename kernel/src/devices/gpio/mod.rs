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

pub struct GeneralGpio<T: blueos_hal::gpio::OutputPin> {
    inner: &'static T,
}

impl<T: blueos_hal::gpio::OutputPin> !Sync for GeneralGpio<T> {}

pub(crate) enum Level {
    Low,
    High,
}

impl<T: blueos_hal::gpio::OutputPin> GeneralGpio<T> {
    pub fn new(inner: &'static T, level: Option<Level>) -> Self {
        let mut gpio = GeneralGpio { inner };
        if let Some(level) = level {
            gpio.set_level(level).ok();
        }
        gpio
    }

    fn set_level(&mut self, level: Level) -> crate::drivers::Result<()> {
        match level {
            Level::Low => self.inner.set_low().map_err(|_| crate::error::code::EIO),
            Level::High => self.inner.set_high().map_err(|_| crate::error::code::EIO),
        }
    }
}

#[cfg(use_embedded_hal_v1)]
impl<T: blueos_hal::gpio::OutputPin> embedded_hal::digital::ErrorType for GeneralGpio<T> {
    type Error = crate::error::Error;
}

#[cfg(use_embedded_hal_v1)]
impl embedded_hal::digital::Error for crate::error::Error {
    fn kind(&self) -> embedded_hal::digital::ErrorKind {
        // FIXME: Map the error code to embedded_hal::digital::ErrorKind
        embedded_hal::digital::ErrorKind::Other
    }
}

#[cfg(use_embedded_hal_v1)]
impl<T: blueos_hal::gpio::OutputPin> embedded_hal::digital::OutputPin for GeneralGpio<T> {
    fn set_low(&mut self) -> Result<(), Self::Error> {
        self.inner.set_low().map_err(|_| crate::error::code::EIO)
    }

    fn set_high(&mut self) -> Result<(), Self::Error> {
        self.inner.set_high().map_err(|_| crate::error::code::EIO)
    }
}
