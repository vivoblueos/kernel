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

use core::cell::Cell;

use crate::{
    devices::{Device, DeviceClass, DeviceId, DeviceManager},
    sync::SpinLock,
};
use alloc::{string::String, sync::Arc};
use embedded_io::ErrorKind;

pub struct GeneralGpio<T: blueos_hal::gpio::OutputPin> {
    inner: &'static T,
    level: Option<Level>,
}

impl<T: blueos_hal::gpio::OutputPin> !Sync for GeneralGpio<T> {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Level {
    Low,
    High,
}

impl<T: blueos_hal::gpio::OutputPin> GeneralGpio<T> {
    pub fn new(inner: &'static T, level: Option<Level>) -> Self {
        let mut gpio = GeneralGpio { inner, level: None };
        if let Some(level) = level {
            gpio.set_level(level).ok();
        }
        gpio
    }

    /// Register this GPIO as a character device.
    ///
    /// Reads return `0\n` or `1\n`; writes accept ASCII `0` or `1`, with
    /// optional surrounding whitespace.
    pub fn register(self, name: String, id: DeviceId) -> Result<(), ErrorKind> {
        let device = Arc::new(GeneralGpioDevice::new(name.clone(), id, self));
        DeviceManager::get().register_device(name, device)
    }

    fn set_level(&mut self, level: Level) -> crate::drivers::Result<()> {
        match level {
            Level::Low => self.inner.set_low().map_err(|_| crate::error::code::EIO)?,
            Level::High => self.inner.set_high().map_err(|_| crate::error::code::EIO)?,
        };
        self.level = Some(level);
        Ok(())
    }
}

struct GeneralGpioDevice<T: blueos_hal::gpio::OutputPin> {
    name: String,
    id: DeviceId,
    inner: SpinLock<&'static T>,
    level: Cell<Option<Level>>,
}

/// Safety: `GeneralGpioDevice` is safe to share between threads
/// because it uses a `SpinLock` to protect access to the
/// underlying GPIO pin, ensuring that only one thread can modify
/// the pin state at a time. The `level` field is a `Cell`,
/// which allows for interior mutability, but since it
/// is only accessed within the locked context, it does not
/// introduce data races. Therefore, it is safe to implement `Sync`
unsafe impl<T: blueos_hal::gpio::OutputPin> Sync for GeneralGpioDevice<T> {}
unsafe impl<T: blueos_hal::gpio::OutputPin> Send for GeneralGpioDevice<T> {}

impl<T: blueos_hal::gpio::OutputPin> GeneralGpioDevice<T> {
    fn new(name: String, id: DeviceId, gpio: GeneralGpio<T>) -> Self {
        Self {
            name,
            id,
            inner: SpinLock::new(gpio.inner),
            level: Cell::new(gpio.level),
        }
    }

    fn set_level(&self, level: Level) -> Result<(), ErrorKind> {
        let l = self.inner.lock();
        let mut current_level = self.level.get();
        match level {
            Level::Low => l.set_low().map_err(|_| ErrorKind::Other)?,
            Level::High => l.set_high().map_err(|_| ErrorKind::Other)?,
        };
        self.level.set(Some(level));
        drop(l);
        Ok(())
    }
}

impl<T: blueos_hal::gpio::OutputPin> Device for GeneralGpioDevice<T> {
    fn name(&self) -> String {
        self.name.clone()
    }

    fn class(&self) -> DeviceClass {
        DeviceClass::Char
    }

    fn id(&self) -> DeviceId {
        self.id
    }

    fn read(&self, pos: u64, buf: &mut [u8], _is_nonblocking: bool) -> Result<usize, ErrorKind> {
        let l = self.inner.lock();
        let level = self.level.get().ok_or(ErrorKind::Other)?;
        let value = match level {
            Level::Low => b"0\n",
            Level::High => b"1\n",
        };
        let pos = usize::try_from(pos).map_err(|_| ErrorKind::InvalidInput)?;
        if pos >= value.len() {
            return Ok(0);
        }

        let len = buf.len().min(value.len() - pos);
        buf[..len].copy_from_slice(&value[pos..pos + len]);
        drop(l);
        Ok(len)
    }

    fn write(&self, _pos: u64, buf: &[u8], _is_nonblocking: bool) -> Result<usize, ErrorKind> {
        let mut values = buf
            .iter()
            .copied()
            .filter(|byte| !byte.is_ascii_whitespace());
        let level = match values.next() {
            Some(b'0') => Level::Low,
            Some(b'1') => Level::High,
            // Formatting helpers may send a trailing newline in a separate
            // write. It has no GPIO value to apply, so accept it as a no-op.
            None => return Ok(buf.len()),
            _ => return Err(ErrorKind::InvalidInput),
        };
        if values.next().is_some() {
            return Err(ErrorKind::InvalidInput);
        }

        self.set_level(level)?;
        Ok(buf.len())
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
        self.set_level(Level::Low)
    }

    fn set_high(&mut self) -> Result<(), Self::Error> {
        self.set_level(Level::High)
    }
}
