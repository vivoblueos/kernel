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

pub struct Null;

impl Null {
    pub fn register() -> Result<(), ErrorKind> {
        let null_dev = Arc::new(Null);
        DeviceManager::get().register_device(String::from("null"), null_dev)
    }
}

impl Device for Null {
    fn name(&self) -> String {
        String::from("null")
    }

    fn class(&self) -> DeviceClass {
        DeviceClass::Char
    }
    fn id(&self) -> DeviceId {
        DeviceId::new(1, 3)
    }

    fn read(&self, _pos: u64, _buf: &mut [u8], _is_blocking: bool) -> Result<usize, ErrorKind> {
        // Always return EOF (0 bytes read)
        Ok(0)
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
    fn test_null_device_read() {
        let null = Null;
        let mut buffer = [0u8; 10];

        // Read should always return 0 bytes (EOF)
        let result = null.read(0, &mut buffer, true);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 0);
    }

    #[test]
    fn test_null_device_write() {
        let null = Null;
        let buffer = [1u8, 2, 3, 4, 5];

        // Write should always succeed and return the buffer length
        let result = null.write(0, &buffer, true);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), buffer.len());
    }

    #[test]
    fn test_null_device_open_close() {
        let null = Null;

        // Test opening with valid flags
        let result = null.open();
        assert!(result.is_ok());

        // Test closing
        let result = null.close();
        assert!(result.is_ok());
    }

    #[test]
    fn test_null_device_id() {
        let null = Null;
        let id = null.id();

        assert_eq!(id.major(), 1);
        assert_eq!(id.minor(), 3);
    }
}
