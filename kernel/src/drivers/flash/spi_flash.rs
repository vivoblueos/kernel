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
use blueos_driver::spi::SpiConfig;
use blueos_hal::{gpio::OutputPin, spi::Spi, PlatPeri};
use core::cmp::min;
use embedded_hal::spi::SpiDevice;
use embedded_io::ErrorKind;

use crate::{
    devices::{
        block::{Block, BlockDriverOps, BlockError, ErrorType},
        bus::{Bus, BusInterface},
        spi_core::block_spi::{BlockSpi, HalOutputPinAdapter, SpinLockDevice},
        DeviceData, DeviceManager,
    },
    drivers::{
        flash::spi_flash_cmd::{FlashError, SpiFlashCmd},
        DriverModule, InitDriver,
    },
    sync::SpinLock,
};

const FLASH_SECTOR_SIZE: u16 = blueos_kconfig::CONFIG_SPI_FLASH_SECTOR_SIZE as u16;
const FLASH_PAGE_SIZE: usize = blueos_kconfig::CONFIG_SPI_FLASH_PAGE_SIZE as usize;
const FLASH_ERASE_SIZE: usize = blueos_kconfig::CONFIG_SPI_FLASH_ERASE_SIZE as usize;
const PAGES_PER_ERASE_BLOCK: usize = FLASH_ERASE_SIZE / FLASH_PAGE_SIZE;
const MAX_24BIT_CAPACITY: u64 = blueos_kconfig::CONFIG_SPI_FLASH_MAX_CAPACITY as u64;
const ERASE_CACHE_SLOTS: usize = 2;
const SECTOR_ERASE_SIZE: usize = 4096;
const BLOCK_ERASE_32K_SIZE: usize = 32768;
const BLOCK_ERASE_64K_SIZE: usize = 65536;

const _: () = {
    assert!(FLASH_ERASE_SIZE % FLASH_PAGE_SIZE == 0);
    assert!(FLASH_ERASE_SIZE % FLASH_SECTOR_SIZE as usize == 0);
    assert!(matches!(
        FLASH_ERASE_SIZE,
        SECTOR_ERASE_SIZE | BLOCK_ERASE_32K_SIZE | BLOCK_ERASE_64K_SIZE
    ));
    assert!(MAX_24BIT_CAPACITY >= FLASH_ERASE_SIZE as u64);
};

fn capacity_from_jedec_id(jedec_id: u32) -> Result<u64, FlashError> {
    let density = (jedec_id & 0xFF) as u32;
    let capacity = 1u64.checked_shl(density).ok_or(FlashError::NotReady)?;
    if capacity < FLASH_ERASE_SIZE as u64 || capacity % FLASH_ERASE_SIZE as u64 != 0 {
        return Err(FlashError::NotReady);
    }
    if capacity > MAX_24BIT_CAPACITY {
        return Err(FlashError::InvalidParam(
            "capacity exceeds configured maximum",
        ));
    }
    Ok(capacity)
}

/// Flash block driver error.
#[derive(Debug, Clone, Eq, PartialEq, thiserror::Error)]
pub enum FlashBlockError {
    #[error("Flash error: {0}")]
    Flash(#[from] FlashError),
}

struct EraseCacheSlot {
    erase_block_id: Option<usize>,
    data: Vec<u8>,
    dirty: bool,
    last_used: u64,
}

impl EraseCacheSlot {
    fn new() -> Self {
        Self {
            erase_block_id: None,
            data: vec![0u8; FLASH_ERASE_SIZE],
            dirty: false,
            last_used: 0,
        }
    }
}

/// SPI NOR Flash block driver with two write-back cache slots.
pub struct SpiFlashBlockDriver<SPI: SpiDevice<u8>> {
    flash_cmd: SpiFlashCmd<SPI>,
    capacity_bytes: u64,
    cache: [EraseCacheSlot; ERASE_CACHE_SLOTS],
    use_counter: u64,
}

impl<SPI: SpiDevice<u8> + Send> SpiFlashBlockDriver<SPI> {
    pub fn new(flash_cmd: SpiFlashCmd<SPI>, capacity_bytes: u64) -> Self {
        SpiFlashBlockDriver {
            flash_cmd,
            capacity_bytes,
            cache: [EraseCacheSlot::new(), EraseCacheSlot::new()],
            use_counter: 0,
        }
    }

    fn cached_slot(&self, erase_block_id: usize) -> Option<usize> {
        self.cache
            .iter()
            .position(|slot| slot.erase_block_id == Some(erase_block_id))
    }

    fn touch_slot(&mut self, slot: usize) {
        self.use_counter = self.use_counter.saturating_add(1);
        self.cache[slot].last_used = self.use_counter;
    }

    fn load_slot(&mut self, slot: usize, erase_block_id: usize) -> Result<(), FlashError> {
        let addr = erase_block_id * FLASH_ERASE_SIZE;
        self.cache[slot].erase_block_id = None;
        self.cache[slot].dirty = false;
        self.flash_cmd
            .read(addr as u32, &mut self.cache[slot].data)?;
        self.cache[slot].erase_block_id = Some(erase_block_id);
        self.cache[slot].dirty = false;
        Ok(())
    }

    fn flush_slot(&mut self, slot: usize) -> Result<(), FlashError> {
        if !self.cache[slot].dirty {
            return Ok(());
        }
        let erase_block_id = self.cache[slot]
            .erase_block_id
            .ok_or(FlashError::NotReady)?;
        let addr = (erase_block_id * FLASH_ERASE_SIZE) as u32;

        match FLASH_ERASE_SIZE {
            SECTOR_ERASE_SIZE => self.flash_cmd.sector_erase(addr)?,
            BLOCK_ERASE_32K_SIZE => self.flash_cmd.block_erase_32k(addr)?,
            BLOCK_ERASE_64K_SIZE => self.flash_cmd.block_erase_64k(addr)?,
            _ => return Err(FlashError::InvalidParam("unsupported erase size")),
        }

        for page_idx in 0..PAGES_PER_ERASE_BLOCK {
            let page_offset = page_idx * FLASH_PAGE_SIZE;
            let page_data = &self.cache[slot].data[page_offset..page_offset + FLASH_PAGE_SIZE];
            self.flash_cmd
                .page_program(addr + page_offset as u32, page_data)?;
        }

        self.cache[slot].dirty = false;
        Ok(())
    }

    fn ensure_erase_block(&mut self, block_id: usize) -> Result<usize, FlashError> {
        let erase_block_id = block_id / (FLASH_ERASE_SIZE / FLASH_SECTOR_SIZE as usize);
        if let Some(slot) = self.cached_slot(erase_block_id) {
            self.touch_slot(slot);
            return Ok(slot);
        }

        let slot = if let Some(slot) = self
            .cache
            .iter()
            .position(|entry| entry.erase_block_id.is_none())
        {
            slot
        } else {
            self.cache
                .iter()
                .enumerate()
                .min_by_key(|(_, entry)| entry.last_used)
                .map(|(index, _)| index)
                .ok_or(FlashError::NotReady)?
        };

        self.flush_slot(slot)?;
        self.load_slot(slot, erase_block_id)?;
        self.touch_slot(slot);
        Ok(slot)
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
        // Process requests across erase-block boundaries.
        let mut cur_block = block_id;
        let mut buf_off = 0usize;
        while buf_off < buf.len() {
            let erase_block_id = cur_block / (FLASH_ERASE_SIZE / FLASH_SECTOR_SIZE as usize);
            let offset = self.block_offset_in_erase(cur_block);
            let chunk = min(buf.len() - buf_off, FLASH_ERASE_SIZE - offset);

            if let Some(slot) = self.cached_slot(erase_block_id) {
                buf[buf_off..buf_off + chunk]
                    .copy_from_slice(&self.cache[slot].data[offset..offset + chunk]);
                self.touch_slot(slot);
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
        // Process requests across erase-block boundaries.
        let mut cur_block = block_id;
        let mut buf_off = 0usize;
        while buf_off < buf.len() {
            let slot = self
                .ensure_erase_block(cur_block)
                .map_err(|e| BlockError::Driver(FlashBlockError::Flash(e)))?;
            let offset = self.block_offset_in_erase(cur_block);
            let chunk = min(buf.len() - buf_off, FLASH_ERASE_SIZE - offset);
            let source = &buf[buf_off..buf_off + chunk];
            let target = &mut self.cache[slot].data[offset..offset + chunk];
            if target != source {
                target.copy_from_slice(source);
                self.cache[slot].dirty = true;
            }
            buf_off += chunk;
            cur_block += chunk / FLASH_SECTOR_SIZE as usize;
        }
        Ok(())
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        for slot in 0..ERASE_CACHE_SLOTS {
            self.flush_slot(slot)
                .map_err(|e| BlockError::Driver(FlashBlockError::Flash(e)))?;
        }
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
    let capacity_bytes = capacity_from_jedec_id(jedec_id).map_err(|e| match e {
        FlashError::NotReady | FlashError::JedecMismatch { .. } => ErrorKind::NotFound,
        FlashError::Timeout => ErrorKind::TimedOut,
        _ => ErrorKind::InvalidInput,
    })?;

    let block_driver = SpiFlashBlockDriver::new(flash_cmd, capacity_bytes);

    let block = Block::<BlockError<FlashBlockError>, { FLASH_SECTOR_SIZE as usize }>::new(
        name,
        Arc::new(SpinLock::new(block_driver)),
    )?;

    DeviceManager::get()
        .register_device(String::from(name), Arc::new(block))
        .map_err(|_| ErrorKind::AlreadyExists)?;

    Ok(())
}

pub struct SpiFlashConfig<G: OutputPin> {
    pub name: &'static str,
    pub cs: &'static G,
}

impl<G: OutputPin> SpiFlashConfig<G> {
    pub const fn new(name: &'static str, cs: &'static G) -> Self {
        SpiFlashConfig { name, cs }
    }
}

#[cfg(use_embedded_hal_v1)]
impl<T, G> InitDriver<BlockSpi<T>> for SpiFlashConfig<G>
where
    T: PlatPeri + Spi<SpiConfig, ()>,
    G: PlatPeri + OutputPin,
{
    type Data = ();

    fn init(self, bus: &Bus<BlockSpi<T>>) -> crate::drivers::Result<Self::Data> {
        let flash_cs = HalOutputPinAdapter::new(self.cs);
        let spi_device = SpinLockDevice::new(bus.intf.clone(), flash_cs, crate::sync::KernelDelay)
            .map_err(|_| crate::error::code::EIO)?;
        let mut flash_cmd = SpiFlashCmd::new(spi_device);

        let jedec_id = flash_cmd.jedec_id().map_err(|error| match error {
            FlashError::NotReady | FlashError::JedecMismatch { .. } => crate::error::code::ENODEV,
            FlashError::Timeout => crate::error::code::ETIMEDOUT,
            _ => crate::error::code::EIO,
        })?;
        let capacity_bytes = capacity_from_jedec_id(jedec_id).map_err(|error| match error {
            FlashError::NotReady | FlashError::JedecMismatch { .. } => crate::error::code::ENODEV,
            FlashError::Timeout => crate::error::code::ETIMEDOUT,
            _ => crate::error::code::EIO,
        })?;

        log::info!(
            "SPI flash JEDEC ID: 0x{:06X}, capacity: {} bytes",
            jedec_id,
            capacity_bytes
        );

        let block_driver = SpiFlashBlockDriver::new(flash_cmd, capacity_bytes);
        let block = Block::<BlockError<FlashBlockError>, { FLASH_SECTOR_SIZE as usize }>::new(
            self.name,
            Arc::new(SpinLock::new(block_driver)),
        )
        .map_err(|_| crate::error::code::EOVERFLOW)?;

        DeviceManager::get()
            .register_device(String::from(self.name), Arc::new(block))
            .map_err(|_| crate::error::code::EEXIST)?;

        Ok(())
    }
}

pub struct SpiFlashDriverModule<G> {
    _marker: core::marker::PhantomData<G>,
}

impl<G> SpiFlashDriverModule<G> {
    pub const fn new() -> Self {
        SpiFlashDriverModule {
            _marker: core::marker::PhantomData,
        }
    }
}

#[cfg(use_embedded_hal_v1)]
impl<T, G> DriverModule<BlockSpi<T>> for SpiFlashDriverModule<G>
where
    T: PlatPeri + Spi<SpiConfig, ()>,
    G: PlatPeri + OutputPin,
{
    type Data = SpiFlashConfig<G>;

    fn probe(dev: &DeviceData) -> crate::drivers::Result<Self::Data> {
        match dev {
            DeviceData::Native(native_dev) => {
                if native_dev.is_attached() {
                    return Err(crate::error::code::ENODEV);
                }
                if let Some(config) = native_dev.config::<SpiFlashConfig<G>>() {
                    Ok(SpiFlashConfig {
                        name: config.name,
                        cs: config.cs,
                    })
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

    const TEST_SECTOR_SIZE: usize = FLASH_SECTOR_SIZE as usize;
    const BLOCKS_PER_ERASE: usize = FLASH_ERASE_SIZE / TEST_SECTOR_SIZE;

    #[test]
    fn test_capacity_from_jedec_id_rejects_unsupported_density() {
        assert_eq!(capacity_from_jedec_id(0xEF4008), Err(FlashError::NotReady));
        assert_eq!(
            capacity_from_jedec_id(0xEF4019),
            Err(FlashError::InvalidParam(
                "capacity exceeds configured maximum"
            ))
        );
    }

    #[test]
    fn test_capacity_from_jedec_id_accepts_w25q64() {
        assert_eq!(capacity_from_jedec_id(0xEF4017), Ok(8 * 1024 * 1024));
    }

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
        assert_eq!(driver.capacity(), 1024 * 1024 / FLASH_SECTOR_SIZE as u64);
        assert_eq!(driver.sector_size(), FLASH_SECTOR_SIZE);
    }

    #[test]
    fn test_read_blocks_from_flash() {
        let (mut driver, shared) = create_block_driver(1024 * 1024);
        let mut buf = [0u8; TEST_SECTOR_SIZE];

        with_shared(&shared, |s| {
            s.read_queue.push(alloc::vec![0xAA; TEST_SECTOR_SIZE]);
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
        let mut write_buf = [0xBB; TEST_SECTOR_SIZE];

        with_shared(&shared, |s| {
            s.read_queue.push(alloc::vec![0u8; FLASH_ERASE_SIZE]);
        });
        driver.write_blocks(0, &write_buf).unwrap();

        let mut read_buf = [0u8; TEST_SECTOR_SIZE];
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
        let write_data = [0xCC; TEST_SECTOR_SIZE];

        with_shared(&shared, |s| {
            s.read_queue.push(alloc::vec![0u8; FLASH_ERASE_SIZE]);
        });

        driver.write_blocks(0, &write_data).unwrap();

        let slot = driver.cached_slot(0).unwrap();
        assert!(driver.cache[slot].dirty);
    }

    #[test]
    fn test_flush_erase_block() {
        let (mut driver, shared) = create_block_driver(1024 * 1024);
        let write_data = [0xDD; TEST_SECTOR_SIZE];

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
        with_shared(&shared, |s| s.writes.clear());
        driver.flush().unwrap();

        let erase_opcode = match FLASH_ERASE_SIZE {
            SECTOR_ERASE_SIZE => 0x20,
            BLOCK_ERASE_32K_SIZE => 0x52,
            BLOCK_ERASE_64K_SIZE => 0xD8,
            _ => unreachable!(),
        };
        with_shared(&shared, |s| assert_eq!(s.writes[2], erase_opcode));
        assert!(driver.cache.iter().all(|slot| !slot.dirty));
    }

    #[test]
    fn test_ensure_erase_block_switching() {
        let (mut driver, shared) = create_block_driver(1024 * 1024);

        with_shared(&shared, |s| {
            s.read_queue.push(alloc::vec![0u8; FLASH_ERASE_SIZE]);
            s.read_queue.push(alloc::vec![0xFF; FLASH_ERASE_SIZE]);
        });

        driver.write_blocks(0, &[0xAA; TEST_SECTOR_SIZE]).unwrap();
        driver
            .write_blocks(BLOCKS_PER_ERASE, &[0xBB; TEST_SECTOR_SIZE])
            .unwrap();

        assert!(driver.cached_slot(0).is_some());
        assert!(driver.cached_slot(1).is_some());
        assert!(driver.cache.iter().all(|slot| slot.dirty));
    }

    #[test]
    fn test_metadata_data_ping_pong_uses_two_cache_slots() {
        let (mut driver, shared) = create_block_driver(1024 * 1024);

        with_shared(&shared, |s| {
            s.read_queue.push(alloc::vec![0u8; FLASH_ERASE_SIZE]);
            s.read_queue.push(alloc::vec![0u8; FLASH_ERASE_SIZE]);
        });

        driver.write_blocks(0, &[0x11; TEST_SECTOR_SIZE]).unwrap();
        driver
            .write_blocks(BLOCKS_PER_ERASE, &[0x22; TEST_SECTOR_SIZE])
            .unwrap();
        driver.write_blocks(0, &[0x33; TEST_SECTOR_SIZE]).unwrap();

        with_shared(&shared, |s| {
            assert_eq!(s.read_queue.len(), 0);
            assert_eq!(s.transaction_count, 2);
        });
        assert!(driver.cached_slot(0).is_some());
        assert!(driver.cached_slot(1).is_some());
        assert!(driver.cache.iter().all(|slot| slot.dirty));
    }

    #[test]
    fn test_block_offset_in_erase() {
        let (driver, _shared) = create_block_driver(1024 * 1024);
        assert_eq!(driver.block_offset_in_erase(0), 0);
        assert_eq!(
            driver.block_offset_in_erase(BLOCKS_PER_ERASE - 1),
            FLASH_ERASE_SIZE - TEST_SECTOR_SIZE
        );
        assert_eq!(driver.block_offset_in_erase(BLOCKS_PER_ERASE), 0);
        assert_eq!(
            driver.block_offset_in_erase(BLOCKS_PER_ERASE + 1),
            TEST_SECTOR_SIZE
        );
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
        let mut buf = [0u8; TEST_SECTOR_SIZE];

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
