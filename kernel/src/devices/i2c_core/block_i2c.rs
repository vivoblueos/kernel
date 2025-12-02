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

use blueos_driver::i2c::I2cConfig;
use blueos_hal::PlatPeri;

// use embedded_hal::i2c::I2c;

pub struct BlockI2c<T: PlatPeri> {
    inner: &'static T,
}

impl<T: blueos_hal::i2c::I2c<I2cConfig, ()>> BlockI2c<T> {
    pub fn write_bytes(
        &mut self,
        address: u8,
        bytes: impl IntoIterator<Item = u8>,
    ) -> Result<(), blueos_hal::err::HalError> {
        let mut peekable = bytes.into_iter().peekable();
        if peekable.peek().is_none() {
            return Err(blueos_hal::err::HalError::InvalidParam);
        }

        self.inner.start_writing(address as u16)?;
        while let Some(byte) = peekable.next() {
            if peekable.peek().is_none() {
                self.inner.send_byte_with_stop(byte)?;
            } else {
                self.inner.write_data8(byte);
            }
        }

        Ok(())
    }

    pub fn read_bytes(
        &mut self,
        address: u8,
        buffer: &mut [u8],
    ) -> Result<(), blueos_hal::err::HalError> {
        todo!()
    }
}

// impl<T: PlatPeri> embedded_hal::i2c::ErrorType for BlockI2c<T> {
//     type Error = blueos_hal::err::HalError;
// }

// impl<T: blueos_hal::i2c::I2c<I2cConfig, ()>> I2c for BlockI2c<T> {
//     fn transaction(
//         &mut self,
//         address: u8,
//         operations: &mut [embedded_hal::i2c::Operation<'_>],
//     ) -> Result<(), Self::Error> {
//         let mut operations = operations.into_iter().peekable();

//         while let Some(operation) = operations.next() {
//             match operation {
//                 embedded_hal::i2c::Operation::Read(buf) => {
//                     self.read_bytes(address, buf)?;
//                 }
//                 embedded_hal::i2c::Operation::Write(buf) => {
//                     self.write_bytes(address, buf.iter().cloned())?;
//                 }
//             }
//         }

//         Ok(())
//     }
// }
