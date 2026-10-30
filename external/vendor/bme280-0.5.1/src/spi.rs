//! BME280 driver for sensors attached via SPI.

#[cfg(feature = "async")]
use core::future::Future;
#[cfg(feature = "sync")]
use embedded_hal::delay::DelayNs;
#[cfg(feature = "sync")]
use embedded_hal::spi::SpiDevice;
#[cfg(feature = "async")]
use embedded_hal_async::delay::DelayNs as AsyncDelayNs;
#[cfg(feature = "async")]
use embedded_hal_async::spi::SpiDevice as AsyncSpiDevice;

#[cfg(feature = "async")]
use super::{AsyncBME280Common, AsyncInterface};
#[cfg(feature = "sync")]
use super::{BME280Common, Interface};
use super::{
    Configuration, Error, IIRFilter, Measurements, Oversampling, BME280_H_CALIB_DATA_LEN,
    BME280_P_T_CALIB_DATA_LEN, BME280_P_T_H_DATA_LEN,
};

/// Representation of a BME280
#[maybe_async_cfg::maybe(
    sync(
        feature = "sync",
        self = "BME280",
        idents(
            AsyncBME280Common(sync = "BME280Common"),
            AsyncSPIInterface(sync = "SPIInterface"),
        )
    ),
    async(feature = "async", keep_self)
)]
#[derive(Debug, Default)]
pub struct AsyncBME280<SPI> {
    common: AsyncBME280Common<AsyncSPIInterface<SPI>>,
}

#[maybe_async_cfg::maybe(
    sync(
        feature = "sync",
        self = "BME280",
        idents(
            AsyncSpiDevice(sync = "SpiDevice"),
            AsyncSpiBus(sync = "SpiBus"),
            AsyncSPIInterface(sync = "SPIInterface"),
            AsyncDelayNs(sync = "DelayNs"),
            AsyncBME280Common(sync = "BME280Common"),
        )
    ),
    async(feature = "async", keep_self)
)]
impl<SPI, SPIE> AsyncBME280<SPI>
where
    SPI: AsyncSpiDevice<Error = SPIE>,
    // SPI::Buf: AsyncSpiBus<u8>,
{
    /// Create a new BME280 struct
    pub fn new(spi: SPI) -> Result<Self, Error<SPIError<SPIE>>> {
        Ok(Self {
            common: AsyncBME280Common {
                interface: AsyncSPIInterface { spi },
                calibration: None,
            },
        })
    }

    /// Initializes the BME280.
    /// This configures 2x temperature oversampling, 16x pressure oversampling, and the IIR filter
    /// coefficient 16.
    pub async fn init<D: AsyncDelayNs>(
        &mut self,
        delay: &mut D,
    ) -> Result<(), Error<SPIError<SPIE>>> {
        self.common
            .init(
                delay,
                Configuration::default()
                    .with_humidity_oversampling(Oversampling::Oversampling1X)
                    .with_pressure_oversampling(Oversampling::Oversampling16X)
                    .with_temperature_oversampling(Oversampling::Oversampling2X)
                    .with_iir_filter(IIRFilter::Coefficient16),
            )
            .await
    }

    /// Initializes the BME280, applying the given configuration.
    pub async fn init_with_config<D: AsyncDelayNs>(
        &mut self,
        delay: &mut D,
        config: Configuration,
    ) -> Result<(), Error<SPIError<SPIE>>> {
        self.common.init(delay, config).await
    }

    /// Captures and processes sensor data for temperature, pressure, and humidity
    pub async fn measure<D: AsyncDelayNs>(
        &mut self,
        delay: &mut D,
    ) -> Result<Measurements<SPIError<SPIE>>, Error<SPIError<SPIE>>> {
        self.common.measure(delay).await
    }
}

/// Register access functions for SPI
#[maybe_async_cfg::maybe(
    sync(feature = "sync", self = "SPIInterface",),
    async(feature = "async", keep_self)
)]
#[derive(Debug, Default)]
struct AsyncSPIInterface<SPI> {
    /// concrete SPI device implementation
    spi: SPI,
}

#[cfg(feature = "sync")]
impl<SPI> Interface for SPIInterface<SPI>
where
    SPI: SpiDevice,
    // SPI::Buf: SpiBus<u8>,
{
    type Error = SPIError<SPI::Error>;

    fn read_register(&mut self, register: u8) -> Result<u8, Error<Self::Error>> {
        let mut result = [0u8];
        self.read_any_register(register, &mut result)?;
        Ok(result[0])
    }

    fn read_data(
        &mut self,
        register: u8,
    ) -> Result<[u8; BME280_P_T_H_DATA_LEN], Error<Self::Error>> {
        let mut data = [0; BME280_P_T_H_DATA_LEN];
        self.read_any_register(register, &mut data)?;
        Ok(data)
    }

    fn read_pt_calib_data(
        &mut self,
        register: u8,
    ) -> Result<[u8; BME280_P_T_CALIB_DATA_LEN], Error<Self::Error>> {
        let mut data = [0; BME280_P_T_CALIB_DATA_LEN];
        self.read_any_register(register, &mut data)?;
        Ok(data)
    }

    fn read_h_calib_data(
        &mut self,
        register: u8,
    ) -> Result<[u8; BME280_H_CALIB_DATA_LEN], Error<Self::Error>> {
        let mut data = [0; BME280_H_CALIB_DATA_LEN];
        self.read_any_register(register, &mut data)?;
        Ok(data)
    }

    fn write_register(&mut self, register: u8, payload: u8) -> Result<(), Error<Self::Error>> {
        // If the first bit is 0, the register is written.
        let transfer = [register & 0x7f, payload];
        self.spi
            .transfer(&mut [], &transfer)
            .map_err(|e| Error::Bus(SPIError::SPI(e)))?;
        Ok(())
    }
}

#[cfg(feature = "async")]
impl<SPI> AsyncInterface for AsyncSPIInterface<SPI>
where
    SPI: AsyncSpiDevice,
    // SPI::Buf: AsyncSpiBus<u8>,
{
    type Error = SPIError<SPI::Error>;

    type ReadRegisterFuture<'a> = impl Future<Output = Result<u8, Error<Self::Error>>>
    where
        SPI: 'a;
    fn read_register(&mut self, register: u8) -> Self::ReadRegisterFuture<'_> {
        async move {
            let mut result = [0u8];
            self.read_any_register(register, &mut result).await?;
            Ok(result[0])
        }
    }

    type ReadDataFuture<'a> = impl Future<Output = Result<[u8; BME280_P_T_H_DATA_LEN], Error<Self::Error>>>
    where
        SPI: 'a;
    fn read_data(&mut self, register: u8) -> Self::ReadDataFuture<'_> {
        async move {
            let mut data = [0; BME280_P_T_H_DATA_LEN];
            self.read_any_register(register, &mut data).await?;
            Ok(data)
        }
    }

    type ReadPtCalibDataFuture<'a> = impl Future<Output = Result<[u8; BME280_P_T_CALIB_DATA_LEN], Error<Self::Error>>>
    where
        SPI: 'a;
    fn read_pt_calib_data(&mut self, register: u8) -> Self::ReadPtCalibDataFuture<'_> {
        async move {
            let mut data = [0; BME280_P_T_CALIB_DATA_LEN];
            self.read_any_register(register, &mut data).await?;
            Ok(data)
        }
    }

    type ReadHCalibDataFuture<'a> = impl Future<Output = Result<[u8; BME280_H_CALIB_DATA_LEN], Error<Self::Error>>>
    where
        SPI: 'a;
    fn read_h_calib_data(&mut self, register: u8) -> Self::ReadHCalibDataFuture<'_> {
        async move {
            let mut data = [0; BME280_H_CALIB_DATA_LEN];
            self.read_any_register(register, &mut data).await?;
            Ok(data)
        }
    }

    type WriteRegisterFuture<'a> = impl Future<Output = Result<(), Error<Self::Error>>>
    where
        SPI: 'a;
    fn write_register(&mut self, register: u8, payload: u8) -> Self::WriteRegisterFuture<'_> {
        async move {
            // If the first bit is 0, the register is written.
            let transfer = [register & 0x7f, payload];
            self.spi
                .transfer(&mut [], &transfer)
                .await
                .map_err(|e| Error::Bus(SPIError::SPI(e)))?;
            Ok(())
        }
    }
}

#[maybe_async_cfg::maybe(
    sync(
        feature = "sync",
        self = "SPIInterface",
        idents(AsyncSpiDevice(sync = "SpiDevice"), AsyncSpiBus(sync = "SpiBus"),)
    ),
    async(feature = "async", keep_self)
)]
impl<SPI> AsyncSPIInterface<SPI>
where
    SPI: AsyncSpiDevice,
    // SPI::Buf: AsyncSpiBus<u8>,
{
    async fn read_any_register(
        &mut self,
        register: u8,
        data: &mut [u8],
    ) -> Result<(), Error<SPIError<SPI::Error>>> {
        self.spi
            .transfer(data, &[register])
            .await
            .map_err(|e| Error::Bus(SPIError::SPI(e)))?;
        Ok(())
    }
}

/// Error which occurred during an SPI transaction
#[derive(Clone, Copy, Debug)]
pub enum SPIError<SPIE> {
    /// The SPI implementation returned an error
    SPI(SPIE),
}
