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

use crate::devices::bus::{BusInterface, BusWrapper};

pub struct BlockI2c<T: PlatPeri> {
    inner: &'static T,
}

impl<T: blueos_hal::i2c::I2c<I2cConfig, ()>> BlockI2c<T> {
    pub fn new(inner: &'static T) -> Result<Self, blueos_hal::err::HalError> {
        inner.configure(&I2cConfig {
            baudrate: 1_000_000,
        })?;
        Ok(BlockI2c { inner })
    }

    pub fn write_bytes(
        &self,
        address: u8,
        bytes: &[u8],
        first_transaction: bool,
        last_transaction: bool,
    ) -> Result<(), blueos_hal::err::HalError> {
        if bytes.is_empty() {
            if !first_transaction {
                // if buffer is empty and not first transaction,
                // release bus
                self.inner.release_bus()?;
            }
            return Err(blueos_hal::err::HalError::InvalidParam);
        }

        let mut abrt_ret = Ok(());
        let mut peekable = bytes.into_iter().peekable();

        'outer: while let Some(byte) = peekable.next() {
            while self.inner.is_tx_fifo_full() {
                // Detect error
                if self.inner.get_error_status() != 0 {
                    self.inner.clear_error_status();
                    abrt_ret = Err(blueos_hal::err::HalError::Fail);
                    break 'outer;
                }
            }

            if peekable.peek().is_none() && last_transaction {
                self.inner.send_byte_with_stop(*byte)?;
            } else {
                self.inner.write_data8(*byte);
            }
        }

        // TODO: if err occurs, wait for transfer complete

        abrt_ret
    }

    pub fn read_bytes(
        &self,
        address: u8,
        buffer: &mut [u8],
        first_transaction: bool,
        last_transaction: bool,
    ) -> Result<(), blueos_hal::err::HalError> {
        if buffer.is_empty() {
            if !first_transaction {
                // if buffer is empty and not first transaction,
                // release bus
                self.inner.release_bus()?;
            }
            return Err(blueos_hal::err::HalError::InvalidParam);
        }

        let lastindex = buffer.len() - 1;
        for (i, byte) in buffer.iter_mut().enumerate() {
            let last_byte = i == lastindex;

            if last_byte && last_transaction {
                *byte = self.inner.read_byte_with_stop()?;
            } else {
                *byte = self.inner.read_data8()?;
            }
        }

        Ok(())
    }
}

impl<T: blueos_hal::i2c::I2c<I2cConfig, ()>> BusInterface for BlockI2c<T> {
    type Region = (bool, u8, bool);

    fn read_region(&self, region: Self::Region, buffer: &mut [u8]) -> crate::drivers::Result<()> {
        let (first, address, last) = region;
        self.read_bytes(address, buffer, first, last)
            .map_err(|_| crate::error::code::EIO)?;
        Ok(())
    }

    fn write_region(&self, region: Self::Region, data: &[u8]) -> crate::drivers::Result<()> {
        let (first, address, last) = region;
        self.write_bytes(address, data, first, last)
            .map_err(|_| crate::error::code::EIO)?;
        Ok(())
    }
}

#[cfg(use_bme280)]
impl<T: blueos_hal::i2c::I2c<I2cConfig, ()>> embedded_hal::i2c::ErrorType
    for BusWrapper<BlockI2c<T>>
{
    type Error = crate::error::Error;
}

#[cfg(use_bme280)]
impl embedded_hal::i2c::Error for crate::error::Error {
    fn kind(&self) -> embedded_hal::i2c::ErrorKind {
        match *self {
            crate::error::code::EIO => embedded_hal::i2c::ErrorKind::Bus,
            _ => embedded_hal::i2c::ErrorKind::Other,
        }
    }
}

#[cfg(use_bme280)]
impl<T: blueos_hal::i2c::I2c<I2cConfig, ()>> embedded_hal::i2c::I2c for BusWrapper<BlockI2c<T>> {
    fn transaction(
        &mut self,
        address: u8,
        operations: &mut [embedded_hal::i2c::Operation<'_>],
    ) -> Result<(), Self::Error> {
        let mut operations = operations.into_iter().peekable();
        self.0
            .lock()
            .inner
            .set_address(address as u16)
            .map_err(|_| crate::error::code::EACCES)?;
        // FIXME: More efficient implementation
        let inner = self.0.lock();

        // Every first transaction should clear the bus state
        let mut first = true;

        while let Some(operation) = operations.next() {
            let last = operations.peek().is_none();
            match operation {
                embedded_hal::i2c::Operation::Read(buf) => {
                    inner.read_region((first, address, last), buf)?
                }
                embedded_hal::i2c::Operation::Write(buf) => {
                    inner.write_region((first, address, last), buf)?
                }
            };
            first = false;
        }

        Ok(())
    }
}
