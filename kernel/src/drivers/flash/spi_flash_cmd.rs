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

//! JEDEC 25-series SPI NOR Flash command layer.

use embedded_hal::spi::{ErrorKind, Operation, SpiDevice};

/// SPI NOR Flash command layer error.
#[derive(Debug, Clone, Eq, PartialEq, thiserror::Error)]
pub enum FlashError {
    #[error("SPI bus error: {0:?}")]
    Spi(ErrorKind),
    #[error("Device not ready")]
    NotReady,
    #[error("JEDEC ID mismatch: expected 0x{expected:06X}, got 0x{got:06X}")]
    JedecMismatch { expected: u32, got: u32 },
    #[error("Write enable failed")]
    WriteEnableFailed,
    #[error("Timeout")]
    Timeout,
    #[error("Address 0x{addr:08X} exceeds 24-bit range")]
    AddrOverflow { addr: u32 },
    #[error("Invalid parameter: {0}")]
    InvalidParam(&'static str),
}

// Inline closure rather than a From impl to avoid coherence issues with the
// generic SPI::Error type parameter.
fn spi_err_to_flash<E: embedded_hal::spi::Error>(err: E) -> FlashError {
    FlashError::Spi(err.kind())
}

/// JEDEC 25-series SPI NOR Flash command layer.
pub struct SpiFlashCmd<SPI: SpiDevice<u8>> {
    spi: SPI,
}

impl<SPI: SpiDevice<u8>> SpiFlashCmd<SPI> {
    pub fn new(spi: SPI) -> Self {
        SpiFlashCmd { spi }
    }

    /// Read JEDEC manufacturer + device ID (command 0x9F).
    pub fn jedec_id(&mut self) -> Result<u32, FlashError> {
        let mut id_buf = [0u8; 3];
        self.spi
            .transaction(&mut [Operation::Write(&[0x9F]), Operation::Read(&mut id_buf)])
            .map_err(spi_err_to_flash)?;
        Ok((id_buf[0] as u32) << 16 | (id_buf[1] as u32) << 8 | (id_buf[2] as u32))
    }

    /// Normal read, 3-byte address (command 0x03).
    pub fn read(&mut self, addr: u32, buf: &mut [u8]) -> Result<(), FlashError> {
        let addr_bytes = addr_bytes(addr)?;
        self.spi
            .transaction(&mut [
                Operation::Write(&[0x03, addr_bytes[0], addr_bytes[1], addr_bytes[2]]),
                Operation::Read(buf),
            ])
            .map_err(spi_err_to_flash)?;
        Ok(())
    }

    /// Fast read, 3-byte address + dummy cycles (command 0x0B).
    pub fn fast_read(&mut self, addr: u32, buf: &mut [u8]) -> Result<(), FlashError> {
        let addr_bytes = addr_bytes(addr)?;
        self.spi
            .transaction(&mut [
                Operation::Write(&[0x0B, addr_bytes[0], addr_bytes[1], addr_bytes[2]]),
                Operation::DelayNs(1_000_000),
                Operation::Read(buf),
            ])
            .map_err(spi_err_to_flash)?;
        Ok(())
    }

    /// Page program: write-enable, then program up to 256 bytes (command 0x02).
    pub fn page_program(&mut self, addr: u32, data: &[u8]) -> Result<(), FlashError> {
        if addr % 256 != 0 {
            return Err(FlashError::InvalidParam(
                "page_program address not 256-byte aligned",
            ));
        }
        if data.len() > 256 {
            return Err(FlashError::InvalidParam(
                "page_program data exceeds 256 bytes",
            ));
        }
        self.write_enable()?;
        let addr_bytes = addr_bytes(addr)?;
        self.spi
            .transaction(&mut [
                Operation::Write(&[0x02, addr_bytes[0], addr_bytes[1], addr_bytes[2]]),
                Operation::Write(data),
            ])
            .map_err(spi_err_to_flash)?;
        self.wait_busy()?;
        Ok(())
    }

    /// 4KB sector erase (command 0x20).
    pub fn sector_erase(&mut self, addr: u32) -> Result<(), FlashError> {
        self.write_enable()?;
        let addr_bytes = addr_bytes(addr)?;
        self.spi
            .transaction(&mut [Operation::Write(&[
                0x20,
                addr_bytes[0],
                addr_bytes[1],
                addr_bytes[2],
            ])])
            .map_err(spi_err_to_flash)?;
        self.wait_busy()?;
        Ok(())
    }

    /// 32KB block erase (command 0x52).
    pub fn block_erase_32k(&mut self, addr: u32) -> Result<(), FlashError> {
        self.write_enable()?;
        let addr_bytes = addr_bytes(addr)?;
        self.spi
            .transaction(&mut [Operation::Write(&[
                0x52,
                addr_bytes[0],
                addr_bytes[1],
                addr_bytes[2],
            ])])
            .map_err(spi_err_to_flash)?;
        self.wait_busy()?;
        Ok(())
    }

    /// 64KB block erase (command 0xD8).
    pub fn block_erase_64k(&mut self, addr: u32) -> Result<(), FlashError> {
        self.write_enable()?;
        let addr_bytes = addr_bytes(addr)?;
        self.spi
            .transaction(&mut [Operation::Write(&[
                0xD8,
                addr_bytes[0],
                addr_bytes[1],
                addr_bytes[2],
            ])])
            .map_err(spi_err_to_flash)?;
        self.wait_busy()?;
        Ok(())
    }

    /// Full chip erase (command 0xC7).
    pub fn chip_erase(&mut self) -> Result<(), FlashError> {
        self.write_enable()?;
        self.spi
            .transaction(&mut [Operation::Write(&[0xC7])])
            .map_err(spi_err_to_flash)?;
        self.wait_busy()?;
        Ok(())
    }

    /// Set Write Enable Latch and verify it took effect (command 0x06).
    pub fn write_enable(&mut self) -> Result<(), FlashError> {
        self.spi
            .transaction(&mut [Operation::Write(&[0x06])])
            .map_err(spi_err_to_flash)?;
        let status = self.read_status()?;
        if status & 0x02 == 0 {
            return Err(FlashError::WriteEnableFailed);
        }
        Ok(())
    }

    /// Read status register byte (command 0x05).
    pub fn read_status(&mut self) -> Result<u8, FlashError> {
        let mut status_buf = [0u8; 1];
        self.spi
            .transaction(&mut [Operation::Write(&[0x05]), Operation::Read(&mut status_buf)])
            .map_err(spi_err_to_flash)?;
        Ok(status_buf[0])
    }

    /// Poll the BUSY bit until clear, or return Timeout after 1000 iterations.
    pub fn wait_busy(&mut self) -> Result<(), FlashError> {
        for _ in 0..1000 {
            let status = self.read_status()?;
            if status & 0x01 == 0 {
                return Ok(());
            }
            self.spi
                .transaction(&mut [Operation::DelayNs(1_000_000)])
                .map_err(spi_err_to_flash)?;
        }
        Err(FlashError::Timeout)
    }

    /// Release from deep power-down (command 0xAB).
    pub fn release_from_deep_power_down(&mut self) -> Result<(), FlashError> {
        self.spi
            .transaction(&mut [Operation::Write(&[0xAB])])
            .map_err(spi_err_to_flash)?;
        Ok(())
    }
}

/// Split a 24-bit address into 3 MSB-first bytes, rejecting >= 16MB.
fn addr_bytes(addr: u32) -> Result<[u8; 3], FlashError> {
    if addr >= 0x0100_0000 {
        return Err(FlashError::AddrOverflow { addr });
    }
    Ok([
        ((addr >> 16) & 0xFF) as u8,
        ((addr >> 8) & 0xFF) as u8,
        (addr & 0xFF) as u8,
    ])
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::sync::Arc;
    use blueos_test_macro::test;
    use core::cell::UnsafeCell;

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

    // MockSpiDevice is accessed exclusively under SpinLock in tests, so sharing
    // the UnsafeCell across threads is sound.
    unsafe impl Send for MockSpiDevice {}
    unsafe impl Sync for MockSpiDevice {}

    impl embedded_hal::spi::ErrorType for MockSpiDevice {
        type Error = MockSpiError;
    }

    #[derive(Debug, Clone, Copy)]
    struct MockSpiError;

    impl embedded_hal::spi::Error for MockSpiError {
        fn kind(&self) -> ErrorKind {
            ErrorKind::Other
        }
    }

    impl embedded_hal::spi::SpiDevice<u8> for MockSpiDevice {
        fn transaction(&mut self, operations: &mut [Operation<'_, u8>]) -> Result<(), Self::Error> {
            let shared = self.shared.get();
            // SAFETY: MockSpiDevice is always wrapped in SpinLock which guarantees
            // exclusive access. No concurrent access possible.
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
                            let read_data = &shared.read_queue[0];
                            let len = buf.len().min(read_data.len());
                            buf[..len].copy_from_slice(&read_data[..len]);
                            if read_data.len() <= buf.len() {
                                shared.read_queue.remove(0);
                            }
                        }
                    }
                    Operation::Transfer(read_buf, write_buf) => {
                        shared.writes.extend_from_slice(write_buf);
                        if !shared.read_queue.is_empty() {
                            let read_data = &shared.read_queue[0];
                            let len = read_buf.len().min(read_data.len());
                            read_buf[..len].copy_from_slice(&read_data[..len]);
                            if read_data.len() <= read_buf.len() {
                                shared.read_queue.remove(0);
                            }
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

    fn create_flash_cmd() -> (SpiFlashCmd<MockSpiDevice>, Arc<UnsafeCell<MockSpiShared>>) {
        let shared = Arc::new(UnsafeCell::new(MockSpiShared::new()));
        let mock = MockSpiDevice::new(Arc::clone(&shared));
        let flash_cmd = SpiFlashCmd::new(mock);
        (flash_cmd, shared)
    }

    fn with_shared<R>(
        shared: &Arc<UnsafeCell<MockSpiShared>>,
        f: impl FnOnce(&mut MockSpiShared) -> R,
    ) -> R {
        // SAFETY: test-only, single-threaded context.
        f(unsafe { &mut *shared.get() })
    }

    #[test]
    fn test_addr_bytes_valid() {
        let result = addr_bytes(0x000000);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), [0x00, 0x00, 0x00]);

        let result = addr_bytes(0x00FFFFFF);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), [0xFF, 0xFF, 0xFF]);

        let result = addr_bytes(0x001234);
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), [0x00, 0x12, 0x34]);
    }

    #[test]
    fn test_addr_bytes_overflow() {
        let result = addr_bytes(0x01000000);
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err(),
            FlashError::AddrOverflow { addr: 0x01000000 }
        );

        let result = addr_bytes(0xFFFFFFFF);
        assert!(result.is_err());
    }

    #[test]
    fn test_jedec_id() {
        let (mut flash_cmd, shared) = create_flash_cmd();
        with_shared(&shared, |s| {
            s.read_queue = alloc::vec![alloc::vec![0xEF, 0x40, 0x18]];
        });

        let jedec_id = flash_cmd.jedec_id().unwrap();
        assert_eq!(jedec_id, 0xEF4018);

        with_shared(&shared, |s| {
            assert_eq!(&s.writes, &[0x9F]);
            assert_eq!(s.transaction_count, 1);
        });
    }

    #[test]
    fn test_read_command() {
        let (mut flash_cmd, shared) = create_flash_cmd();
        let mut buf = [0u8; 4];
        with_shared(&shared, |s| {
            s.read_queue = alloc::vec![alloc::vec![0xAA, 0xBB, 0xCC, 0xDD]];
        });

        flash_cmd.read(0x001000, &mut buf).unwrap();
        assert_eq!(buf, [0xAA, 0xBB, 0xCC, 0xDD]);

        with_shared(&shared, |s| {
            assert_eq!(&s.writes, &[0x03, 0x00, 0x10, 0x00]);
        });
    }

    #[test]
    fn test_read_addr_overflow() {
        let (mut flash_cmd, _shared) = create_flash_cmd();
        let mut buf = [0u8; 4];
        let result = flash_cmd.read(0x01000000, &mut buf);
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err(),
            FlashError::AddrOverflow { addr: 0x01000000 }
        );
    }

    #[test]
    fn test_fast_read_command() {
        let (mut flash_cmd, shared) = create_flash_cmd();
        let mut buf = [0u8; 4];
        with_shared(&shared, |s| {
            s.read_queue = alloc::vec![alloc::vec![0x11, 0x22, 0x33, 0x44]];
        });

        flash_cmd.fast_read(0x000100, &mut buf).unwrap();
        assert_eq!(buf, [0x11, 0x22, 0x33, 0x44]);

        with_shared(&shared, |s| {
            assert_eq!(&s.writes[..4], &[0x0B, 0x00, 0x01, 0x00]);
            assert!(s.delays > 0);
        });
    }

    #[test]
    fn test_page_program_param_validation() {
        let (mut flash_cmd, _shared) = create_flash_cmd();
        let data = [0u8; 128];

        let result = flash_cmd.page_program(0x001001, &data);
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err(),
            FlashError::InvalidParam("page_program address not 256-byte aligned")
        );

        let big_data = alloc::vec![0u8; 300];
        let result = flash_cmd.page_program(0x000000, &big_data);
        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err(),
            FlashError::InvalidParam("page_program data exceeds 256 bytes")
        );
    }

    #[test]
    fn test_page_program_success() {
        let (mut flash_cmd, shared) = create_flash_cmd();
        with_shared(&shared, |s| {
            s.read_queue = alloc::vec![alloc::vec![0x02], alloc::vec![0x00]];
        });

        let data = [0xAA, 0xBB, 0xCC, 0xDD];
        flash_cmd.page_program(0x000000, &data).unwrap();

        with_shared(&shared, |s| {
            let writes = &s.writes;
            assert_eq!(writes[0], 0x06);
            assert_eq!(writes[1], 0x05);
            assert_eq!(&writes[2..6], &[0x02, 0x00, 0x00, 0x00]);
            assert_eq!(&writes[6..10], &[0xAA, 0xBB, 0xCC, 0xDD]);
            assert_eq!(writes[10], 0x05);
        });
    }

    #[test]
    fn test_sector_erase_command() {
        let (mut flash_cmd, shared) = create_flash_cmd();
        with_shared(&shared, |s| {
            s.read_queue = alloc::vec![alloc::vec![0x02], alloc::vec![0x00]];
        });

        flash_cmd.sector_erase(0x001000).unwrap();

        with_shared(&shared, |s| {
            let writes = &s.writes;
            assert_eq!(writes[0], 0x06);
            assert_eq!(writes[1], 0x05);
            assert_eq!(writes[2], 0x20);
            assert_eq!(&writes[3..6], &[0x00, 0x10, 0x00]);
            assert_eq!(writes[6], 0x05);
        });
    }

    #[test]
    fn test_write_enable_success() {
        let (mut flash_cmd, shared) = create_flash_cmd();
        with_shared(&shared, |s| {
            s.read_queue = alloc::vec![alloc::vec![0x02]];
        });

        flash_cmd.write_enable().unwrap();

        with_shared(&shared, |s| {
            assert_eq!(s.writes[0], 0x06);
            assert_eq!(s.writes[1], 0x05);
        });
    }

    #[test]
    fn test_write_enable_failed() {
        let (mut flash_cmd, shared) = create_flash_cmd();
        with_shared(&shared, |s| {
            s.read_queue = alloc::vec![alloc::vec![0x00]];
        });

        let result = flash_cmd.write_enable();
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), FlashError::WriteEnableFailed);
    }

    #[test]
    fn test_read_status() {
        let (mut flash_cmd, shared) = create_flash_cmd();
        with_shared(&shared, |s| {
            s.read_queue = alloc::vec![alloc::vec![0x03]];
        });

        let status = flash_cmd.read_status().unwrap();
        assert_eq!(status, 0x03);

        with_shared(&shared, |s| {
            assert_eq!(s.writes[0], 0x05);
        });
    }

    #[test]
    fn test_chip_erase_command() {
        let (mut flash_cmd, shared) = create_flash_cmd();
        with_shared(&shared, |s| {
            s.read_queue = alloc::vec![alloc::vec![0x02], alloc::vec![0x00]];
        });

        flash_cmd.chip_erase().unwrap();

        with_shared(&shared, |s| {
            assert_eq!(s.writes[0], 0x06);
            assert_eq!(s.writes[1], 0x05);
            assert_eq!(s.writes[2], 0xC7);
            assert_eq!(s.writes[3], 0x05);
        });
    }

    #[test]
    fn test_release_from_deep_power_down() {
        let (mut flash_cmd, shared) = create_flash_cmd();
        flash_cmd.release_from_deep_power_down().unwrap();

        with_shared(&shared, |s| {
            assert_eq!(&s.writes, &[0xAB]);
        });
    }

    #[test]
    fn test_block_erase_32k_command() {
        let (mut flash_cmd, shared) = create_flash_cmd();
        with_shared(&shared, |s| {
            s.read_queue = alloc::vec![alloc::vec![0x02], alloc::vec![0x00]];
        });

        flash_cmd.block_erase_32k(0x001000).unwrap();

        with_shared(&shared, |s| {
            let writes = &s.writes;
            assert_eq!(writes[0], 0x06);
            assert_eq!(writes[1], 0x05);
            assert_eq!(writes[2], 0x52);
            assert_eq!(&writes[3..6], &[0x00, 0x10, 0x00]);
            assert_eq!(writes[6], 0x05);
        });
    }

    #[test]
    fn test_block_erase_64k_command() {
        let (mut flash_cmd, shared) = create_flash_cmd();
        with_shared(&shared, |s| {
            s.read_queue = alloc::vec![alloc::vec![0x02], alloc::vec![0x00]];
        });

        flash_cmd.block_erase_64k(0x001000).unwrap();

        with_shared(&shared, |s| {
            let writes = &s.writes;
            assert_eq!(writes[0], 0x06);
            assert_eq!(writes[1], 0x05);
            assert_eq!(writes[2], 0xD8);
            assert_eq!(&writes[3..6], &[0x00, 0x10, 0x00]);
            assert_eq!(writes[6], 0x05);
        });
    }

    #[test]
    fn test_wait_busy_timeout() {
        let (mut flash_cmd, shared) = create_flash_cmd();
        with_shared(&shared, |s| {
            s.read_queue = alloc::vec![alloc::vec![0x01]; 1000];
        });

        let result = flash_cmd.wait_busy();
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), FlashError::Timeout);

        with_shared(&shared, |s| {
            assert_eq!(s.transaction_count, 2000);
            assert_eq!(s.delays, 1000);
        });
    }

    #[test]
    fn test_spi_error_propagation() {
        let (mut flash_cmd, shared) = create_flash_cmd();
        with_shared(&shared, |s| {
            s.should_fail = true;
        });

        let result = flash_cmd.jedec_id();
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), FlashError::Spi(ErrorKind::Other));
    }
}
