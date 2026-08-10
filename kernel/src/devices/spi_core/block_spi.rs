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

use crate::sync::KernelDelay;
use blueos_driver::spi::SpiConfig;
use blueos_hal::PlatPeri;
use embedded_hal::spi::Operation;

use crate::devices::bus::{BusInterface, BusWrapper};

pub struct BlockSpi<T: PlatPeri, G: blueos_hal::gpio::OutputPin> {
    inner: &'static T,
    cs: &'static G,
}

impl<T: blueos_hal::spi::Spi<SpiConfig, ()>, G: blueos_hal::gpio::OutputPin> BlockSpi<T, G> {
    pub fn new(
        inner: &'static T,
        cs: &'static G,
        config: &SpiConfig,
    ) -> Result<Self, blueos_hal::err::HalError> {
        inner.configure(config)?;
        Ok(BlockSpi { inner, cs })
    }

    pub fn assert_cs(&self) {
        self.cs.set_low().ok();
    }

    pub fn deassert_cs(&self) {
        self.cs.set_high().ok();
    }

    fn read(&mut self, words: &mut [u8]) -> Result<(), crate::error::Error> {
        self.inner.read(words).map_err(|_| crate::error::code::EIO)
    }

    fn write(&mut self, words: &[u8]) -> Result<(), crate::error::Error> {
        self.inner.write(words).map_err(|_| crate::error::code::EIO)
    }

    fn transfer(&mut self, read: &mut [u8], write: &[u8]) -> Result<(), crate::error::Error> {
        self.inner
            .transfer(read, write)
            .map_err(|_| crate::error::code::EIO)
    }

    fn transfer_in_place(&mut self, words: &mut [u8]) -> Result<(), crate::error::Error> {
        self.inner
            .write(words)
            .map_err(|_| crate::error::code::EIO)?;
        self.inner.read(words).map_err(|_| crate::error::code::EIO)
    }

    fn flush(&mut self) -> Result<(), crate::error::Error> {
        Ok(())
    }
}

impl<T: blueos_hal::spi::Spi<SpiConfig, ()>, G: blueos_hal::gpio::OutputPin> BusInterface
    for BlockSpi<T, G>
{
    type Region = ();

    fn read_region(&self, region: Self::Region, buffer: &mut [u8]) -> crate::drivers::Result<()> {
        todo!()
    }

    fn write_region(&self, region: Self::Region, data: &[u8]) -> crate::drivers::Result<()> {
        todo!()
    }
}

#[cfg(use_embedded_hal_v1)]
impl<T: blueos_hal::spi::Spi<SpiConfig, ()>, G: blueos_hal::gpio::OutputPin>
    embedded_hal::spi::ErrorType for BusWrapper<BlockSpi<T, G>>
{
    type Error = crate::error::Error;
}

#[cfg(use_embedded_hal_v1)]
impl embedded_hal::spi::Error for crate::error::Error {
    fn kind(&self) -> embedded_hal::spi::ErrorKind {
        // FIXME: Map the error code to embedded_hal::spi::ErrorKind
        embedded_hal::spi::ErrorKind::Other
    }
}

#[cfg(use_embedded_hal_v1)]
impl<T: blueos_hal::spi::Spi<SpiConfig, ()>, G: blueos_hal::gpio::OutputPin>
    embedded_hal::spi::SpiDevice<u8> for BusWrapper<BlockSpi<T, G>>
{
    fn transaction(&mut self, operations: &mut [Operation<'_, u8>]) -> Result<(), Self::Error> {
        let mut inner = self.0.lock();
        inner.assert_cs();

        let op_res = operations.iter_mut().try_for_each(|op| match op {
            Operation::Read(buf) => inner.read(buf),
            Operation::Write(buf) => inner.write(buf),
            Operation::Transfer(read, write) => inner.transfer(read, write),
            Operation::TransferInPlace(buf) => inner.transfer_in_place(buf),
            Operation::DelayNs(ns) => {
                use embedded_hal::delay::DelayNs;
                inner.flush()?;
                let mut kernel = KernelDelay;
                kernel.delay_ns(*ns);
                Ok(())
            }
        });

        let flush_res = inner.flush();
        inner.deassert_cs();
        op_res?;
        flush_res?;

        Ok(())
    }
}
