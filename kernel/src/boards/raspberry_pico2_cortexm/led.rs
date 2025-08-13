// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{
    devices::{Device, DeviceId, DeviceManager},
    sync::SpinLock,
};
use alloc::{format, string::String, sync::Arc};
use embedded_hal::digital::OutputPin;

pub struct Led<P: OutputPin> {
    index: u32,
    pin: SpinLock<P>,
}

impl<P: OutputPin> Led<P> {
    pub fn new(index: u32, pin: P) -> Self {
        Led {
            index,
            pin: SpinLock::new(pin),
        }
    }
}

impl<P: OutputPin + Send + Sync> Device for Led<P> {
    fn name(&self) -> String {
        format!("led{}", self.index)
    }

    fn class(&self) -> crate::devices::DeviceClass {
        crate::devices::DeviceClass::Char
    }

    fn id(&self) -> DeviceId {
        DeviceId::new(6, self.index as usize)
    }

    fn open(&self) -> Result<(), embedded_io::ErrorKind> {
        // Initialize the LED hardware here if needed
        Ok(())
    }

    fn close(&self) -> Result<(), embedded_io::ErrorKind> {
        // Clean up the LED hardware here if needed
        Ok(())
    }

    fn read(
        &self,
        _pos: u64,
        _buf: &mut [u8],
        _is_nonblocking: bool,
    ) -> Result<usize, embedded_io::ErrorKind> {
        // Reading from LED doesn't make sense, return an error
        Err(embedded_io::ErrorKind::Unsupported)
    }

    fn write(
        &self,
        _pos: u64,
        buf: &[u8],
        is_nonblocking: bool,
    ) -> Result<usize, embedded_io::ErrorKind> {
        // Writing to the LED hardware here
        if buf.is_empty() {
            return Err(embedded_io::ErrorKind::InvalidInput);
        }

        if buf.contains(&b'1') {
            let _ = self.pin.irqsave_lock().set_high();
        } else if buf.contains(&b'0') {
            let _ = self.pin.irqsave_lock().set_low();
        } else {
            return Err(embedded_io::ErrorKind::InvalidInput);
        }

        Ok(buf.len())
    }
}

pub fn led_init(pin: Arc<dyn Device>) -> Result<(), embedded_io::ErrorKind> {
    DeviceManager::get().register_device(String::from("led0"), pin)?;
    Ok(())
}
