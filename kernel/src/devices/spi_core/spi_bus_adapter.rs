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

//! SPI bus adapter — HAL `Spi` trait → `embedded_hal::spi::SpiBus<u8>`
//!
//! Wraps a HAL `Spi` peripheral into an `embedded_hal::spi::SpiBus<u8>`,
//! the bus-level interface that device drivers consume via
//! `ExclusiveDevice<SpiBus, OutputPin>` for full `SpiDevice<u8>` with CS management.

use blueos_driver::spi::SpiConfig;
use blueos_hal::PlatPeri;

/// SPI bus adapter (bus-level)
///
/// Wraps a HAL `Spi` peripheral into an `embedded_hal::spi::SpiBus<u8>`.
/// CS management is handled separately by `ExclusiveDevice` combining
/// this bus with a GPIO `OutputPin` (e.g., `Esp32GpioOutputPin`).
pub struct SpiBusAdapter<T: PlatPeri> {
    inner: &'static T,
}

impl<T: blueos_hal::spi::Spi<SpiConfig, ()>> SpiBusAdapter<T> {
    /// Create a new SpiBusAdapter, configuring the underlying HAL peripheral
    /// with SPI NOR Flash default settings (Mode 0, 20MHz, MSB-first).
    pub fn new(inner: &'static T) -> Result<Self, blueos_hal::err::HalError> {
        inner.configure(&SpiConfig::spi_flash_default())?;
        Ok(SpiBusAdapter { inner })
    }
}

impl<T: blueos_hal::spi::Spi<SpiConfig, ()>> embedded_hal::spi::ErrorType for SpiBusAdapter<T> {
    type Error = SpiBusAdapterError;
}

/// SPI bus adapter error type — maps HAL errors to embedded-hal's SPI error framework.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum SpiBusAdapterError {
    /// Error originating from the underlying HAL Spi peripheral
    HalError,
}

impl embedded_hal::spi::Error for SpiBusAdapterError {
    fn kind(&self) -> embedded_hal::spi::ErrorKind {
        match self {
            SpiBusAdapterError::HalError => embedded_hal::spi::ErrorKind::Other,
        }
    }
}

/// SpiBus<u8> implementation — bridges HAL Spi to embedded-hal SpiBus.
/// The HAL peripheral already waits for completion after each transfer, so `flush()` is a no-op.
impl<T: blueos_hal::spi::Spi<SpiConfig, ()>> embedded_hal::spi::SpiBus<u8> for SpiBusAdapter<T> {
    fn read(&mut self, words: &mut [u8]) -> Result<(), Self::Error> {
        self.inner
            .read(words)
            .map_err(|_| SpiBusAdapterError::HalError)
    }

    fn write(&mut self, words: &[u8]) -> Result<(), Self::Error> {
        self.inner
            .write(words)
            .map_err(|_| SpiBusAdapterError::HalError)
    }

    fn transfer(&mut self, read: &mut [u8], write: &[u8]) -> Result<(), Self::Error> {
        self.inner
            .transfer(read, write)
            .map_err(|_| SpiBusAdapterError::HalError)
    }

    fn transfer_in_place(&mut self, words: &mut [u8]) -> Result<(), Self::Error> {
        // Write then read back into same buffer (two-step since HAL transfer can't alias)
        self.inner
            .write(words)
            .map_err(|_| SpiBusAdapterError::HalError)?;
        self.inner
            .read(words)
            .map_err(|_| SpiBusAdapterError::HalError)
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        // Esp32Spi2 waits for completion after each transfer, so bus is always idle
        Ok(())
    }
}

/// Adapts a `blueos_hal::gpio::OutputPin` to `embedded_hal::digital::OutputPin`,
/// so a HAL pin can feed `embedded_hal_bus::spi::ExclusiveDevice` (CS bound).
pub struct HalOutputPinAdapter<P: blueos_hal::gpio::OutputPin>(pub P);

impl<P: blueos_hal::gpio::OutputPin> embedded_hal::digital::ErrorType for HalOutputPinAdapter<P> {
    type Error = core::convert::Infallible;
}

impl<P: blueos_hal::gpio::OutputPin> embedded_hal::digital::OutputPin for HalOutputPinAdapter<P> {
    fn set_low(&mut self) -> Result<(), Self::Error> {
        let _ = self.0.set_low();
        Ok(())
    }

    fn set_high(&mut self) -> Result<(), Self::Error> {
        let _ = self.0.set_high();
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_hal::err::{HalError, Result as HalResult};
    use blueos_test_macro::test;
    use core::sync::atomic::{AtomicUsize, Ordering};
    use embedded_hal::spi::SpiBus;

    /// Mock HAL Spi peripheral for testing SpiBusAdapter.
    /// Implements all required HAL traits (PlatPeri, Configuration, Spi).
    static MOCK_SPI: MockHalSpi = MockHalSpi;

    struct MockHalSpi;

    // PlatPeri: required by Spi supertrait (Sync + Send + 'static)
    impl blueos_hal::PlatPeri for MockHalSpi {
        fn enable(&self) {}
        fn disable(&self) {}
    }

    // Configuration<SpiConfig>: required by Spi supertrait
    impl blueos_hal::Configuration<SpiConfig> for MockHalSpi {
        type Target = ();
        fn configure(&self, _param: &SpiConfig) -> HalResult<Self::Target> {
            Ok(())
        }
    }

    // Spi<SpiConfig, ()>: required for SpiBusAdapter::new and SpiBus impl
    impl blueos_hal::spi::Spi<SpiConfig, ()> for MockHalSpi {
        fn transfer(&self, read: &mut [u8], write: &[u8]) -> HalResult<()> {
            if SHOULD_FAIL.load(Ordering::Relaxed) != 0 {
                return Err(HalError::Fail);
            }
            // Copy write data into read buffer (simulates SPI loopback)
            let len = read.len().min(write.len());
            read[..len].copy_from_slice(&write[..len]);
            WRITE_COUNT.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }

        fn read(&self, buf: &mut [u8]) -> HalResult<()> {
            if SHOULD_FAIL.load(Ordering::Relaxed) != 0 {
                return Err(HalError::Fail);
            }
            let data = READ_DATA.load(Ordering::Relaxed) as u8;
            for byte in buf.iter_mut() {
                *byte = data;
            }
            READ_COUNT.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }

        fn write(&self, buf: &[u8]) -> HalResult<()> {
            if SHOULD_FAIL.load(Ordering::Relaxed) != 0 {
                return Err(HalError::Fail);
            }
            LAST_WRITE_LEN.store(buf.len(), Ordering::Relaxed);
            WRITE_COUNT.fetch_add(1, Ordering::Relaxed);
            Ok(())
        }
    }

    static WRITE_COUNT: AtomicUsize = AtomicUsize::new(0);
    static READ_COUNT: AtomicUsize = AtomicUsize::new(0);
    static LAST_WRITE_LEN: AtomicUsize = AtomicUsize::new(0);
    static READ_DATA: AtomicUsize = AtomicUsize::new(0);
    static SHOULD_FAIL: AtomicUsize = AtomicUsize::new(0);

    fn reset_counters() {
        WRITE_COUNT.store(0, Ordering::Relaxed);
        READ_COUNT.store(0, Ordering::Relaxed);
        LAST_WRITE_LEN.store(0, Ordering::Relaxed);
        READ_DATA.store(0, Ordering::Relaxed);
        SHOULD_FAIL.store(0, Ordering::Relaxed);
    }

    #[test]
    fn test_spi_bus_adapter_new() {
        let result = SpiBusAdapter::new(&MOCK_SPI);
        assert!(result.is_ok());
    }

    #[test]
    fn test_spi_bus_adapter_write() {
        let mut bus = SpiBusAdapter::new(&MOCK_SPI).unwrap();
        reset_counters();

        bus.write(&[0x9F, 0x00, 0x00, 0x00]).unwrap();
        assert_eq!(WRITE_COUNT.load(Ordering::Relaxed), 1);
        assert_eq!(LAST_WRITE_LEN.load(Ordering::Relaxed), 4);
    }

    #[test]
    fn test_spi_bus_adapter_read() {
        let mut bus = SpiBusAdapter::new(&MOCK_SPI).unwrap();
        reset_counters();
        READ_DATA.store(0xAB, Ordering::Relaxed);

        let mut read_buf = [0u8; 3];
        bus.read(&mut read_buf).unwrap();

        assert_eq!(READ_COUNT.load(Ordering::Relaxed), 1);
        assert_eq!(read_buf, [0xAB, 0xAB, 0xAB]);
    }

    #[test]
    fn test_spi_bus_adapter_transfer() {
        let mut bus = SpiBusAdapter::new(&MOCK_SPI).unwrap();
        reset_counters();

        let mut read_buf = [0u8; 4];
        let write_buf = [0x03, 0x00, 0x10, 0x00];
        bus.transfer(&mut read_buf, &write_buf).unwrap();

        assert_eq!(WRITE_COUNT.load(Ordering::Relaxed), 1);
        // Transfer copies write data into read buffer (loopback behavior)
        assert_eq!(read_buf, write_buf);
    }

    #[test]
    fn test_spi_bus_adapter_transfer_in_place() {
        let mut bus = SpiBusAdapter::new(&MOCK_SPI).unwrap();
        reset_counters();
        READ_DATA.store(0xFF, Ordering::Relaxed);

        let mut buf = [0xAA, 0xBB, 0xCC, 0xDD];
        bus.transfer_in_place(&mut buf).unwrap();

        // TransferInPlace: write then read back (two-step)
        assert_eq!(WRITE_COUNT.load(Ordering::Relaxed), 1);
        assert_eq!(READ_COUNT.load(Ordering::Relaxed), 1);
        assert_eq!(buf, [0xFF, 0xFF, 0xFF, 0xFF]);
    }

    #[test]
    fn test_spi_bus_adapter_flush() {
        let mut bus = SpiBusAdapter::new(&MOCK_SPI).unwrap();
        assert!(bus.flush().is_ok());
    }

    #[test]
    fn test_spi_bus_adapter_error_kind() {
        use embedded_hal::spi::Error as SpiError;

        assert_eq!(
            SpiError::kind(&SpiBusAdapterError::HalError),
            embedded_hal::spi::ErrorKind::Other
        );
    }

    #[test]
    fn test_hal_write_error_propagation() {
        let mut bus = SpiBusAdapter::new(&MOCK_SPI).unwrap();
        reset_counters();
        SHOULD_FAIL.store(1, Ordering::Relaxed);

        let result = bus.write(&[0x9F, 0x00, 0x00, 0x00]);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), SpiBusAdapterError::HalError);
    }

    #[test]
    fn test_hal_read_error_propagation() {
        let mut bus = SpiBusAdapter::new(&MOCK_SPI).unwrap();
        reset_counters();
        SHOULD_FAIL.store(1, Ordering::Relaxed);

        let mut read_buf = [0u8; 3];
        let result = bus.read(&mut read_buf);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), SpiBusAdapterError::HalError);
    }

    #[test]
    fn test_hal_transfer_error_propagation() {
        let mut bus = SpiBusAdapter::new(&MOCK_SPI).unwrap();
        reset_counters();
        SHOULD_FAIL.store(1, Ordering::Relaxed);

        let mut read_buf = [0u8; 4];
        let write_buf = [0x03, 0x00, 0x10, 0x00];
        let result = bus.transfer(&mut read_buf, &write_buf);
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), SpiBusAdapterError::HalError);
    }
}
