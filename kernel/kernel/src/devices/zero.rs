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

use crate::devices::{Device, DeviceClass, DeviceId, DeviceManager};
use alloc::{string::String, sync::Arc};
use embedded_io::ErrorKind;

pub struct Zero;

impl Zero {
    pub fn register() -> Result<(), ErrorKind> {
        let zero = Arc::new(Zero);
        DeviceManager::get().register_device(String::from("zero"), zero)
    }
}

impl Device for Zero {
    fn name(&self) -> String {
        String::from("zero")
    }

    fn class(&self) -> DeviceClass {
        DeviceClass::Char
    }

    fn id(&self) -> DeviceId {
        DeviceId::new(1, 5)
    }

    fn read(&self, _pos: u64, buf: &mut [u8], _is_blocking: bool) -> Result<usize, ErrorKind> {
        // Fill buffer with zeros
        buf.fill(0);
        Ok(buf.len())
    }

    fn write(&self, _pos: u64, buf: &[u8], _is_blocking: bool) -> Result<usize, ErrorKind> {
        // Always succeed, but discard the data
        Ok(buf.len())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn test_zero_device_read() {
        let zero = Zero;
        let mut buffer = [1u8; 10];

        // Read should fill buffer with zeros
        let result = zero.read(0, &mut buffer, true);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), buffer.len());
        assert!(buffer.iter().all(|&x| x == 0));
    }

    #[test]
    fn test_zero_device_write() {
        let zero = Zero;
        let buffer = [1u8, 2, 3, 4, 5];

        // Write should always succeed and return the buffer length
        let result = zero.write(0, &buffer, true);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), buffer.len());
    }

    #[test]
    fn test_zero_device_open_close() {
        let zero = Zero;

        // Test opening with valid flags
        let result = zero.open();
        assert!(result.is_ok());

        // Test closing
        let result = zero.close();
        assert!(result.is_ok());
    }

    #[test]
    fn test_zero_device_id() {
        let zero = Zero;
        let id = zero.id();

        assert_eq!(id.major(), 1);
        assert_eq!(id.minor(), 5);
    }
}
