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

use crate::{
    devices::{virtio::VirtioHal, Device, DeviceClass, DeviceId, DeviceManager},
    sync::SpinLock,
};
use alloc::{string::String, sync::Arc, vec};
use core::cmp::min;
use embedded_io::{Error as IOError, ErrorKind};
use virtio_drivers::{
    device::blk::{VirtIOBlk, SECTOR_SIZE},
    transport::SomeTransport,
    Hal,
};

pub const VIRTUAL_STORAGE_NAME: &str = "virt-storage";

#[derive(Debug, Clone, Eq, PartialEq, thiserror::Error)]
pub enum BlockError<T> {
    #[error("Error from the drviver: {0}")]
    Driver(#[from] T),
}

impl embedded_io::Error for BlockError<virtio_drivers::Error> {
    fn kind(&self) -> ErrorKind {
        match self {
            BlockError::Driver(error) => match error {
                virtio_drivers::Error::QueueFull => ErrorKind::Other,
                virtio_drivers::Error::NotReady => ErrorKind::Other,
                virtio_drivers::Error::WrongToken => ErrorKind::InvalidData,
                virtio_drivers::Error::AlreadyUsed => ErrorKind::Other,
                virtio_drivers::Error::InvalidParam => ErrorKind::InvalidInput,
                virtio_drivers::Error::DmaError => ErrorKind::OutOfMemory,
                virtio_drivers::Error::IoError => ErrorKind::Other,
                virtio_drivers::Error::Unsupported => ErrorKind::Unsupported,
                virtio_drivers::Error::ConfigSpaceTooSmall => ErrorKind::InvalidInput,
                virtio_drivers::Error::ConfigSpaceMissing => ErrorKind::InvalidInput,
                virtio_drivers::Error::SocketDeviceError(_socket_error) => ErrorKind::Other,
            },
        }
    }
}

pub trait ErrorType {
    type Error: embedded_io::Error;
}

pub trait BlockDriverOps: Send + Sync + ErrorType {
    /// Gets the capacity of the block device, in 512 byte ([`SECTOR_SIZE`]) sectors.
    fn capacity(&self) -> u64;
    /// Get the sector size in bytes.
    fn sector_size(&self) -> u16;
    /// Reads one or more blocks into the given buffer.
    fn read_blocks(&mut self, block_id: usize, buf: &mut [u8]) -> Result<(), Self::Error>;
    /// Writes the contents of the given buffer to a block or blocks.
    fn write_blocks(&mut self, block_id: usize, buf: &[u8]) -> Result<(), Self::Error>;
    /// Requests the device to flush any pending writes to storage.
    fn flush(&mut self) -> Result<(), Self::Error>;
}

impl<H: Hal> ErrorType for VirtIOBlk<H, SomeTransport<'static>> {
    type Error = BlockError<virtio_drivers::Error>; // : io::Error
}

impl<H: Hal> BlockDriverOps for VirtIOBlk<H, SomeTransport<'static>> {
    fn capacity(&self) -> u64 {
        self.capacity()
    }

    fn read_blocks(&mut self, block_id: usize, buf: &mut [u8]) -> Result<(), Self::Error> {
        match self.read_blocks(block_id, buf) {
            Ok(_) => Ok(()),
            Err(error) => Err(BlockError::Driver(error)),
        }
    }

    fn write_blocks(&mut self, block_id: usize, buf: &[u8]) -> Result<(), Self::Error> {
        match self.write_blocks(block_id, buf) {
            Ok(_) => Ok(()),
            Err(error) => Err(BlockError::Driver(error)),
        }
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        match self.flush() {
            Ok(_) => Ok(()),
            Err(error) => Err(BlockError::Driver(error)),
        }
    }

    fn sector_size(&self) -> u16 {
        SECTOR_SIZE.try_into().unwrap()
    }
}

pub fn init_virtio_block(
    driver: VirtIOBlk<VirtioHal, SomeTransport<'static>>,
) -> Result<(), ErrorKind> {
    let block = Block::new(VIRTUAL_STORAGE_NAME, Arc::new(SpinLock::new(driver)));
    DeviceManager::get().register_device(String::from(VIRTUAL_STORAGE_NAME), Arc::new(block))
}

pub struct Block<E: embedded_io::Error, const SECTOR_SIZE: usize> {
    driver: Arc<SpinLock<dyn BlockDriverOps<Error = E>>>,
    name: String,
    total_size: u64, // in bytes
}

impl<E: embedded_io::Error> Block<E, SECTOR_SIZE> {
    pub fn new(name: &str, driver: Arc<SpinLock<dyn BlockDriverOps<Error = E>>>) -> Self {
        let total_size = {
            let capacity = driver.lock().capacity();
            capacity * SECTOR_SIZE as u64
        };
        Block {
            driver,
            name: String::from(name),
            total_size,
        }
    }
}

impl<E: embedded_io::Error> Device for Block<E, SECTOR_SIZE> {
    fn name(&self) -> String {
        self.name.clone()
    }

    fn class(&self) -> DeviceClass {
        DeviceClass::Block
    }

    fn id(&self) -> DeviceId {
        todo!()
    }

    fn read(&self, pos: u64, buf: &mut [u8], _is_nonblocking: bool) -> Result<usize, ErrorKind> {
        // TODO: handle nonblocking read
        let max_read = min(buf.len() as u64, self.total_size.saturating_sub(pos)) as usize;
        if max_read == 0 {
            return Ok(0);
        }
        // Calculate starting sector and offset
        let start_sector = (pos / SECTOR_SIZE as u64) as usize;
        let sector_offset = (pos % SECTOR_SIZE as u64) as usize;
        let sectors_coverred = (sector_offset + max_read).div_ceil(SECTOR_SIZE);
        let mut sector_buf = vec![0u8; sectors_coverred * SECTOR_SIZE];
        self.driver
            .lock()
            .read_blocks(start_sector, &mut sector_buf)
            .map_err(|e| IOError::kind(&e))?;
        // Copy to output buffer
        buf[..max_read].copy_from_slice(&sector_buf[sector_offset..sector_offset + max_read]);
        Ok(max_read)
    }

    fn write(&self, pos: u64, buf: &[u8], _is_nonblocking: bool) -> Result<usize, ErrorKind> {
        // TODO: handle nonblocking write
        let total_write_size = min(buf.len() as u64, self.total_size.saturating_sub(pos)) as usize;
        if total_write_size == 0 {
            return Ok(0);
        }
        let mut data = &buf[..total_write_size];
        let mut start_sector = (pos / SECTOR_SIZE as u64) as usize;
        let sector_offset = (pos % SECTOR_SIZE as u64) as usize;

        // 1. Write first sector
        let mut write_size = min(SECTOR_SIZE - sector_offset, total_write_size);
        let mut sector_buf = [0u8; SECTOR_SIZE];
        if sector_offset != 0 || write_size != SECTOR_SIZE {
            // If the content to be written cannot completely cover the sector, it needs to be read out first
            self.driver
                .lock()
                .read_blocks(start_sector, &mut sector_buf)
                .map_err(|e| IOError::kind(&e))?;
        }
        // Update the parts that need to be modified
        sector_buf[sector_offset..sector_offset + write_size].copy_from_slice(&data[..write_size]);
        // Write back to the modified sectors
        self.driver
            .lock()
            .write_blocks(start_sector, &sector_buf)
            .map_err(|e| IOError::kind(&e))?;
        data = &data[write_size..];
        start_sector += 1;
        // 2. Write continuous sectors
        let continuous_sectors = data.len() / SECTOR_SIZE;
        if continuous_sectors != 0 {
            write_size = SECTOR_SIZE * continuous_sectors;
            let mut sector_buf = vec![0u8; write_size];
            sector_buf[..write_size].copy_from_slice(&data[..write_size]);
            // Write back to the modified sectors
            self.driver
                .lock()
                .write_blocks(start_sector, &sector_buf)
                .map_err(|e| IOError::kind(&e))?;
            data = &data[write_size..];
            start_sector += continuous_sectors;
        }
        // 3. Write last sector
        write_size = data.len();
        if write_size > 0 {
            let mut sector_buf = [0u8; SECTOR_SIZE];
            self.driver
                .lock()
                .read_blocks(start_sector, &mut sector_buf)
                .map_err(|e| IOError::kind(&e))?;
            // Update the parts that need to be modified
            sector_buf[..write_size].copy_from_slice(&data[..write_size]);
            // Write back to the modified sectors
            self.driver
                .lock()
                .write_blocks(start_sector, &sector_buf)
                .map_err(|e| IOError::kind(&e))?;
        }
        Ok(total_write_size)
    }

    fn capacity(&self) -> Result<u64, ErrorKind> {
        let driver = self.driver.lock();
        Ok(driver.capacity())
    }

    fn sector_size(&self) -> Result<u16, ErrorKind> {
        let driver = self.driver.lock();
        Ok(driver.sector_size())
    }

    fn sync(&self) -> Result<(), ErrorKind> {
        let mut driver = self.driver.lock();
        match driver.flush() {
            Ok(_) => Ok(()),
            Err(error) => Err(embedded_io::Error::kind(&error)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;
    use semihosting::println;

    fn test_virtio_block_read_write(write_size: usize, pos: usize) {
        let block_device = DeviceManager::get().get_block_device(VIRTUAL_STORAGE_NAME);
        if let Some(block_device) = block_device {
            let first_sector = pos / SECTOR_SIZE;
            let last_sector = (pos + write_size) / SECTOR_SIZE;
            // Fill the fist and last sector with other content
            let mut to_write_first_sector = vec![1u8; pos - first_sector * SECTOR_SIZE];
            let _ = block_device.write(
                (first_sector * SECTOR_SIZE) as u64,
                to_write_first_sector.as_slice(),
                false,
            );
            let mut to_write_last_sector = vec![2u8; (last_sector + 1) * SECTOR_SIZE - pos];
            let _ = block_device.write(
                (pos + write_size) as u64,
                to_write_last_sector.as_slice(),
                false,
            );

            // Check the contents of the location being written
            let to_write = vec![99u8; write_size];
            let _ = block_device.write(pos as u64, to_write.as_slice(), false);
            let mut to_read = vec![0u8; write_size];
            let _ = block_device.read(pos as u64, to_read.as_mut_slice(), false);
            debug_assert!(to_write == to_read);

            // Check that the impact of a write operation does not exceed its expected scope
            let mut to_read_first_sector = vec![3u8; pos - first_sector * SECTOR_SIZE];
            let _ = block_device.read(
                (first_sector * SECTOR_SIZE) as u64,
                to_read_first_sector.as_mut_slice(),
                false,
            );
            let mut to_read_last_sector = vec![4u8; (last_sector + 1) * SECTOR_SIZE - pos];
            let _ = block_device.read(
                (pos + write_size) as u64,
                to_read_last_sector.as_mut_slice(),
                false,
            );
            debug_assert_eq!(to_write_first_sector, to_read_first_sector);
            debug_assert_eq!(to_write_last_sector, to_read_last_sector);
        }
    }

    #[test]
    fn test_block_device_read_write() {
        // an aligned sector
        test_virtio_block_read_write(SECTOR_SIZE, SECTOR_SIZE * 10);
        // aligned sectors
        test_virtio_block_read_write(SECTOR_SIZE * 2, SECTOR_SIZE * 10);
        test_virtio_block_read_write(SECTOR_SIZE * 4, SECTOR_SIZE * 10);
        // an unaligned sector
        test_virtio_block_read_write(SECTOR_SIZE / 2, SECTOR_SIZE * 10 + SECTOR_SIZE / 3);
        test_virtio_block_read_write(SECTOR_SIZE / 2, SECTOR_SIZE * 10);
        test_virtio_block_read_write(SECTOR_SIZE / 2, SECTOR_SIZE * 10 + SECTOR_SIZE / 2);
        // unaligned sectors
        test_virtio_block_read_write(
            SECTOR_SIZE + SECTOR_SIZE / 2,
            SECTOR_SIZE * 10 + SECTOR_SIZE / 3,
        );
        test_virtio_block_read_write(
            SECTOR_SIZE * 3 + SECTOR_SIZE / 3,
            SECTOR_SIZE * 10 + SECTOR_SIZE / 3,
        );
        test_virtio_block_read_write(SECTOR_SIZE * 3 + SECTOR_SIZE / 3, SECTOR_SIZE * 10);
        test_virtio_block_read_write(
            SECTOR_SIZE * 3 + SECTOR_SIZE / 2,
            SECTOR_SIZE * 10 + SECTOR_SIZE / 2,
        );
    }
}
