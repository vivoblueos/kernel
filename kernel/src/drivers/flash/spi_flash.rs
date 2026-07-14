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

//! SPI NOR Flash FTL block driver adapter.

use alloc::{string::String, sync::Arc, vec, vec::Vec};
use blueos_hal::gpio::OutputPin;
use blueos_hal::spi::Spi;
use blueos_hal::PlatPeri;
use blueos_driver::spi::SpiConfig;
use core::cmp::min;
use embedded_hal::spi::SpiDevice;
use embedded_io::ErrorKind;

use crate::{
    devices::{
        block::{Block, BlockDriverOps, BlockError, ErrorType},
        bus::{Bus, BusInterface},
        spi_core::block_spi::BlockSpi,
        DeviceData, DeviceManager,
    },
    drivers::{flash::spi_flash_cmd::{FlashError, SpiFlashCmd}, DriverModule, InitDriver},
    sync::SpinLock,
};

const FLASH_SECTOR_SIZE: u16 = 512;
const FLASH_ERASE_SIZE: usize = 4096;
const PAGES_PER_ERASE_BLOCK: usize = FLASH_ERASE_SIZE / 256;

/// Flash block driver error.
#[derive(Debug, Clone, Eq, PartialEq, thiserror::Error)]
pub enum FlashBlockError {
    #[error("Flash error: {0}")]
    Flash(#[from] FlashError),
}

/// SPI NOR Flash FTL block driver, caching one erase block at a time.
pub struct SpiFlashBlockDriver<SPI: SpiDevice<u8>> {
    flash_cmd: SpiFlashCmd<SPI>,
    capacity_bytes: u64,
    erase_size: usize,
    erase_buf: Vec<u8>,
    dirty: bool,
    current_erase_block: Option<usize>,
}

impl<SPI: SpiDevice<u8> + Send> SpiFlashBlockDriver<SPI> {
    pub fn new(flash_cmd: SpiFlashCmd<SPI>, capacity_bytes: u64) -> Self {
        SpiFlashBlockDriver {
            flash_cmd,
            capacity_bytes,
            erase_size: FLASH_ERASE_SIZE,
            erase_buf: vec![0u8; FLASH_ERASE_SIZE],
            dirty: false,
            current_erase_block: None,
        }
    }

    fn read_erase_block(&mut self, erase_block_id: usize) -> Result<(), FlashError> {
        let addr = erase_block_id * FLASH_ERASE_SIZE;
        self.flash_cmd.read(addr as u32, &mut self.erase_buf)?;
        self.current_erase_block = Some(erase_block_id);
        self.dirty = false;
        Ok(())
    }

    fn flush_erase_block(&mut self) -> Result<(), FlashError> {
        if !self.dirty || self.current_erase_block.is_none() {
            return Ok(());
        }
        let erase_block_id = self.current_erase_block.unwrap();
        let addr = (erase_block_id * FLASH_ERASE_SIZE) as u32;

        self.flash_cmd.sector_erase(addr)?;

        for page_idx in 0..PAGES_PER_ERASE_BLOCK {
            let page_offset = page_idx * 256;
            let page_data = &self.erase_buf[page_offset..page_offset + 256];
            self.flash_cmd
                .page_program(addr + page_offset as u32, page_data)?;
        }

        self.dirty = false;
        Ok(())
    }

    fn ensure_erase_block(&mut self, block_id: usize) -> Result<(), FlashError> {
        let erase_block_id = block_id / (FLASH_ERASE_SIZE / FLASH_SECTOR_SIZE as usize);
        if self.current_erase_block != Some(erase_block_id) {
            self.flush_erase_block()?;
            self.read_erase_block(erase_block_id)?;
        }
        Ok(())
    }

    fn block_offset_in_erase(&self, block_id: usize) -> usize {
        (block_id % (FLASH_ERASE_SIZE / FLASH_SECTOR_SIZE as usize)) * FLASH_SECTOR_SIZE as usize
    }
}

impl<SPI: SpiDevice<u8> + Send + Sync> ErrorType for SpiFlashBlockDriver<SPI> {
    type Error = BlockError<FlashBlockError>;
}

impl<SPI: SpiDevice<u8> + Send + Sync> BlockDriverOps for SpiFlashBlockDriver<SPI> {
    fn capacity(&self) -> u64 {
        self.capacity_bytes / FLASH_SECTOR_SIZE as u64
    }

    fn sector_size(&self) -> u16 {
        FLASH_SECTOR_SIZE
    }

    fn read_blocks(&mut self, block_id: usize, buf: &mut [u8]) -> Result<(), Self::Error> {
        // The cache holds one erase block; chunk across boundaries.
        let mut cur_block = block_id;
        let mut buf_off = 0usize;
        while buf_off < buf.len() {
            let erase_block_id = cur_block / (FLASH_ERASE_SIZE / FLASH_SECTOR_SIZE as usize);
            let offset = self.block_offset_in_erase(cur_block);
            let chunk = min(buf.len() - buf_off, FLASH_ERASE_SIZE - offset);

            if self.dirty && self.current_erase_block == Some(erase_block_id) {
                buf[buf_off..buf_off + chunk]
                    .copy_from_slice(&self.erase_buf[offset..offset + chunk]);
            } else {
                let addr = (cur_block * FLASH_SECTOR_SIZE as usize) as u32;
                self.flash_cmd
                    .read(addr, &mut buf[buf_off..buf_off + chunk])
                    .map_err(|e| BlockError::Driver(FlashBlockError::Flash(e)))?;
            }

            buf_off += chunk;
            cur_block += chunk / FLASH_SECTOR_SIZE as usize;
        }
        Ok(())
    }

    fn write_blocks(&mut self, block_id: usize, buf: &[u8]) -> Result<(), Self::Error> {
        self.ensure_erase_block(block_id)
            .map_err(|e| BlockError::Driver(FlashBlockError::Flash(e)))?;

        let offset = self.block_offset_in_erase(block_id);
        let copy_len = min(buf.len(), FLASH_ERASE_SIZE - offset);
        self.erase_buf[offset..offset + copy_len].copy_from_slice(&buf[..copy_len]);
        self.dirty = true;

        Ok(())
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        self.flush_erase_block()
            .map_err(|e| BlockError::Driver(FlashBlockError::Flash(e)))?;
        Ok(())
    }
}

/// Initialize the SPI NOR Flash block device and register it under `name`.
pub fn init_spi_flash<SPI>(spi: SPI, name: &str) -> Result<(), ErrorKind>
where
    SPI: SpiDevice<u8> + Send + Sync + 'static,
{
    let mut flash_cmd = SpiFlashCmd::new(spi);

    let jedec_id = flash_cmd.jedec_id().map_err(|e| match e {
        FlashError::Spi(_) => ErrorKind::Other,
        FlashError::Timeout => ErrorKind::TimedOut,
        _ => ErrorKind::NotFound,
    })?;
    let density_byte = (jedec_id & 0xFF) as u8;

    let capacity_bytes: u64 = if density_byte < 31 {
        (1u32 << density_byte) as u64
    } else {
        1u64 << density_byte
    };

    let block_driver = SpiFlashBlockDriver::new(flash_cmd, capacity_bytes);

    let block = Block::<BlockError<FlashBlockError>, { FLASH_SECTOR_SIZE as usize }>::new(
        name,
        Arc::new(SpinLock::new(block_driver)),
    );

    DeviceManager::get()
        .register_device(String::from(name), Arc::new(block))
        .map_err(|_| ErrorKind::AlreadyExists)?;

    Ok(())
}

// SPI must be Send + Sync: the driver is shared via SpinLock behind an Arc<dyn
// Device>, so it crosses threads (Send) and is referenced from &self (Sync).
unsafe impl<SPI: SpiDevice<u8> + Send + Sync> Sync for SpiFlashBlockDriver<SPI> {}

#[derive(Default)]
pub struct SpiFlashConfig {
    pub name: &'static str,
}

impl SpiFlashConfig {
    pub const fn new(name: &'static str) -> Self {
        SpiFlashConfig { name }
    }
}

#[cfg(use_embedded_hal_v1)]
impl<T, G> InitDriver<BlockSpi<T, G>> for SpiFlashConfig
where
    T: PlatPeri + Spi<SpiConfig, ()>,
    G: PlatPeri + OutputPin,
{
    type Data = ();

    fn init(self, bus: &Bus<BlockSpi<T, G>>) -> crate::drivers::Result<Self::Data> {
        let mut flash_cmd = SpiFlashCmd::new(bus.intf.clone());

        let jedec_id = flash_cmd
            .jedec_id()
            .map_err(|_| crate::error::code::EIO)?;
        let density_byte = (jedec_id & 0xFF) as u8;
        let capacity_bytes: u64 = if density_byte < 31 {
            (1u32 << density_byte) as u64
        } else {
            1u64 << density_byte
        };

        log::info!(
            "SPI flash JEDEC ID: 0x{:06X}, capacity: {} bytes",
            jedec_id,
            capacity_bytes
        );

        let block_driver = SpiFlashBlockDriver::new(flash_cmd, capacity_bytes);
        let block = Block::<BlockError<FlashBlockError>, { FLASH_SECTOR_SIZE as usize }>::new(
            self.name,
            Arc::new(SpinLock::new(block_driver)),
        );

        DeviceManager::get()
            .register_device(String::from(self.name), Arc::new(block))
            .map_err(|_| crate::error::code::EEXIST)?;

        Ok(())
    }
}

pub struct SpiFlashDriverModule;

#[cfg(use_embedded_hal_v1)]
impl<T, G> DriverModule<BlockSpi<T, G>> for SpiFlashDriverModule
where
    T: PlatPeri + Spi<SpiConfig, ()>,
    G: PlatPeri + OutputPin,
{
    type Data = SpiFlashConfig;

    fn probe(dev: &DeviceData) -> crate::drivers::Result<Self::Data> {
        match dev {
            DeviceData::Native(native_dev) => {
                if native_dev.is_attached() {
                    return Err(crate::error::code::ENODEV);
                }
                if let Some(config) = native_dev.config::<SpiFlashConfig>() {
                    Ok(SpiFlashConfig { name: config.name })
                } else {
                    Err(crate::error::code::ENODEV)
                }
            }
            _ => Err(crate::error::code::ENODEV),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::devices::block::{Block, BlockDriverOps, BlockError, ErrorType};
    use alloc::sync::Arc;
    use blueos_test_macro::test;
    use core::cell::UnsafeCell;
    use embedded_hal::spi::{ErrorKind, Operation, SpiDevice};

    struct MockSpiDevice {
        shared: Arc<UnsafeCell<MockSpiShared>>,
    }

    struct MockSpiShared {
        writes: alloc::vec::Vec<u8>,
        delays: usize,
        read_queue: alloc::vec::Vec<alloc::vec::Vec<u8>>,
        should_fail: bool,
        transaction_count: usize,
    }

    unsafe impl Send for MockSpiDevice {}
    unsafe impl Sync for MockSpiDevice {}

    #[derive(Debug, Clone, Copy)]
    struct MockSpiError;

    impl embedded_hal::spi::ErrorType for MockSpiDevice {
        type Error = MockSpiError;
    }

    impl embedded_hal::spi::Error for MockSpiError {
        fn kind(&self) -> ErrorKind {
            ErrorKind::Other
        }
    }

    impl SpiDevice<u8> for MockSpiDevice {
        fn transaction(&mut self, operations: &mut [Operation<'_, u8>]) -> Result<(), Self::Error> {
            let shared = self.shared.get();
            // SAFETY: single-threaded test context, accessed exclusively.
            let shared = unsafe { &mut *shared };
            shared.transaction_count += 1;

            if shared.should_fail {
                shared.should_fail = false;
                return Err(MockSpiError);
            }

            for op in operations.iter_mut() {
                match op {
                    Operation::Write(data) => {
                        shared.writes.extend_from_slice(data);
                    }
                    Operation::Read(buf) => {
                        if !shared.read_queue.is_empty() {
                            let data = &shared.read_queue[0];
                            let len = buf.len().min(data.len());
                            buf[..len].copy_from_slice(&data[..len]);
                            shared.read_queue.remove(0);
                        }
                    }
                    Operation::Transfer(read_buf, write_buf) => {
                        shared.writes.extend_from_slice(write_buf);
                        if !shared.read_queue.is_empty() {
                            let data = &shared.read_queue[0];
                            let len = read_buf.len().min(data.len());
                            read_buf[..len].copy_from_slice(&data[..len]);
                            shared.read_queue.remove(0);
                        }
                    }
                    Operation::TransferInPlace(buf) => {
                        shared.writes.extend_from_slice(buf);
                    }
                    Operation::DelayNs(_) => {
                        shared.delays += 1;
                    }
                }
            }
            Ok(())
        }
    }

    impl MockSpiDevice {
        fn new(shared: Arc<UnsafeCell<MockSpiShared>>) -> Self {
            MockSpiDevice { shared }
        }
    }

    impl MockSpiShared {
        fn new() -> Self {
            MockSpiShared {
                writes: alloc::vec::Vec::new(),
                delays: 0,
                read_queue: alloc::vec::Vec::new(),
                should_fail: false,
                transaction_count: 0,
            }
        }
    }

    fn with_shared<R>(
        shared: &Arc<UnsafeCell<MockSpiShared>>,
        f: impl FnOnce(&mut MockSpiShared) -> R,
    ) -> R {
        // SAFETY: test-only, single-threaded context.
        f(unsafe { &mut *shared.get() })
    }

    fn create_block_driver(
        capacity_bytes: u64,
    ) -> (
        SpiFlashBlockDriver<MockSpiDevice>,
        Arc<UnsafeCell<MockSpiShared>>,
    ) {
        let shared = Arc::new(UnsafeCell::new(MockSpiShared::new()));
        let mock = MockSpiDevice::new(Arc::clone(&shared));
        let flash_cmd = SpiFlashCmd::new(mock);
        let driver = SpiFlashBlockDriver::new(flash_cmd, capacity_bytes);
        (driver, shared)
    }

    #[test]
    fn test_block_driver_capacity() {
        let (driver, _shared) = create_block_driver(1024 * 1024);
        assert_eq!(driver.capacity(), 1024 * 1024 / 512);
        assert_eq!(driver.sector_size(), 512);
    }

    #[test]
    fn test_read_blocks_from_flash() {
        let (mut driver, shared) = create_block_driver(1024 * 1024);
        let mut buf = [0u8; 512];

        with_shared(&shared, |s| {
            s.read_queue.push(alloc::vec![0xAA; 512]);
        });

        driver.read_blocks(0, &mut buf).unwrap();
        assert_eq!(buf[0], 0xAA);

        with_shared(&shared, |s| {
            assert_eq!(s.writes[0], 0x03);
        });
    }

    #[test]
    fn test_read_blocks_from_dirty_cache() {
        let (mut driver, shared) = create_block_driver(1024 * 1024);
        let mut write_buf = [0xBB; 512];

        with_shared(&shared, |s| {
            s.read_queue.push(alloc::vec![0u8; FLASH_ERASE_SIZE]);
        });
        driver.write_blocks(0, &write_buf).unwrap();

        let mut read_buf = [0u8; 512];
        with_shared(&shared, |s| {
            s.writes.clear();
            s.transaction_count = 0;
        });
        driver.read_blocks(0, &mut read_buf).unwrap();
        assert_eq!(read_buf[0], 0xBB);

        with_shared(&shared, |s| {
            assert_eq!(s.transaction_count, 0);
        });
    }

    #[test]
    fn test_write_marks_dirty() {
        let (mut driver, shared) = create_block_driver(1024 * 1024);
        let write_data = [0xCC; 512];

        with_shared(&shared, |s| {
            s.read_queue.push(alloc::vec![0u8; FLASH_ERASE_SIZE]);
        });

        driver.write_blocks(0, &write_data).unwrap();

        assert!(driver.dirty);
        assert_eq!(driver.current_erase_block, Some(0));
    }

    #[test]
    fn test_flush_erase_block() {
        let (mut driver, shared) = create_block_driver(1024 * 1024);
        let write_data = [0xDD; 512];

        with_shared(&shared, |s| {
            s.read_queue.push(alloc::vec![0u8; FLASH_ERASE_SIZE]);
            s.read_queue.push(alloc::vec![0x02]);
            s.read_queue.push(alloc::vec![0x00]);
            for _ in 0..PAGES_PER_ERASE_BLOCK {
                s.read_queue.push(alloc::vec![0x02]);
                s.read_queue.push(alloc::vec![0x00]);
            }
        });

        driver.write_blocks(0, &write_data).unwrap();
        driver.flush().unwrap();

        assert!(!driver.dirty);
    }

    #[test]
    fn test_ensure_erase_block_switching() {
        let (mut driver, shared) = create_block_driver(1024 * 1024);

        with_shared(&shared, |s| {
            s.read_queue.push(alloc::vec![0u8; FLASH_ERASE_SIZE]);
            s.read_queue.push(alloc::vec![0x02]);
            s.read_queue.push(alloc::vec![0x00]);
            for _ in 0..PAGES_PER_ERASE_BLOCK {
                s.read_queue.push(alloc::vec![0x02]);
                s.read_queue.push(alloc::vec![0x00]);
            }
            s.read_queue.push(alloc::vec![0xFF; FLASH_ERASE_SIZE]);
        });

        driver.write_blocks(0, &[0xAA; 512]).unwrap();
        assert_eq!(driver.current_erase_block, Some(0));

        driver.write_blocks(8, &[0xBB; 512]).unwrap();
        assert_eq!(driver.current_erase_block, Some(1));
    }

    #[test]
    fn test_block_offset_in_erase() {
        let (driver, _shared) = create_block_driver(1024 * 1024);
        assert_eq!(driver.block_offset_in_erase(0), 0);
        assert_eq!(driver.block_offset_in_erase(7), 3584);
        assert_eq!(driver.block_offset_in_erase(8), 0);
        assert_eq!(driver.block_offset_in_erase(9), 512);
    }

    #[test]
    fn test_flush_no_dirty_no_op() {
        let (mut driver, shared) = create_block_driver(1024 * 1024);
        driver.flush().unwrap();

        with_shared(&shared, |s| {
            assert_eq!(s.transaction_count, 0);
        });
    }

    #[test]
    fn test_spi_error_on_read() {
        let (mut driver, shared) = create_block_driver(1024 * 1024);
        let mut buf = [0u8; 512];

        with_shared(&shared, |s| {
            s.should_fail = true;
        });

        let result = driver.read_blocks(0, &mut buf);
        assert!(result.is_err());
    }

    #[test]
    fn test_block_error_kind_mapping() {
        use embedded_io::Error as IOError;

        let err = BlockError::Driver(FlashBlockError::Flash(
            crate::drivers::flash::spi_flash_cmd::FlashError::Spi(ErrorKind::Other),
        ));
        assert_eq!(IOError::kind(&err), embedded_io::ErrorKind::Other);

        let err = BlockError::Driver(FlashBlockError::Flash(
            crate::drivers::flash::spi_flash_cmd::FlashError::NotReady,
        ));
        assert_eq!(IOError::kind(&err), embedded_io::ErrorKind::Other);

        let err = BlockError::Driver(FlashBlockError::Flash(
            crate::drivers::flash::spi_flash_cmd::FlashError::Timeout,
        ));
        assert_eq!(IOError::kind(&err), embedded_io::ErrorKind::TimedOut);

        let err = BlockError::Driver(FlashBlockError::Flash(
            crate::drivers::flash::spi_flash_cmd::FlashError::AddrOverflow { addr: 0x1000000 },
        ));
        assert_eq!(IOError::kind(&err), embedded_io::ErrorKind::InvalidInput);

        let err = BlockError::Driver(FlashBlockError::Flash(
            crate::drivers::flash::spi_flash_cmd::FlashError::JedecMismatch {
                expected: 0xEF4018,
                got: 0x000000,
            },
        ));
        assert_eq!(IOError::kind(&err), embedded_io::ErrorKind::NotFound);

        let err = BlockError::Driver(FlashBlockError::Flash(
            crate::drivers::flash::spi_flash_cmd::FlashError::WriteEnableFailed,
        ));
        assert_eq!(IOError::kind(&err), embedded_io::ErrorKind::Other);

        let err = BlockError::Driver(FlashBlockError::Flash(
            crate::drivers::flash::spi_flash_cmd::FlashError::InvalidParam("test"),
        ));
        assert_eq!(IOError::kind(&err), embedded_io::ErrorKind::InvalidInput);
    }
}
