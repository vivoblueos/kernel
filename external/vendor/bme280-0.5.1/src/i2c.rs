//! BME280 driver for sensors attached via I2C.

#[cfg(feature = "async")]
use core::future::Future;
#[cfg(feature = "sync")]
use embedded_hal::delay::DelayNs;
use embedded_hal::i2c::ErrorType;
#[cfg(feature = "sync")]
use embedded_hal::i2c::I2c;
#[cfg(feature = "async")]
use embedded_hal_async::delay::DelayNs as AsyncDelayNs;
#[cfg(feature = "async")]
use embedded_hal_async::i2c::I2c as AsyncI2c;

#[cfg(feature = "async")]
use super::{AsyncBME280Common, AsyncInterface};
#[cfg(feature = "sync")]
use super::{BME280Common, Interface};
use super::{
    Configuration, Error, IIRFilter, Measurements, Oversampling, BME280_H_CALIB_DATA_LEN,
    BME280_P_T_CALIB_DATA_LEN, BME280_P_T_H_DATA_LEN,
};

const BME280_I2C_ADDR_PRIMARY: u8 = 0x76;
const BME280_I2C_ADDR_SECONDARY: u8 = 0x77;

/// Representation of a BME280
#[maybe_async_cfg::maybe(
    sync(
        feature = "sync",
        self = "BME280",
        idents(AsyncBME280Common(sync = "BME280Common"))
    ),
    async(feature = "async", keep_self)
)]
#[derive(Debug, Default)]
pub struct AsyncBME280<I2C> {
    common: AsyncBME280Common<I2CInterface<I2C>>,
}

#[maybe_async_cfg::maybe(
    sync(
        feature = "sync",
        self = "BME280",
        idents(
            AsyncI2c(sync = "I2c"),
            AsyncDelayNs(sync = "DelayNs"),
            AsyncBME280Common(sync = "BME280Common"),
        )
    ),
    async(feature = "async", keep_self)
)]
impl<I2C> AsyncBME280<I2C>
where
    I2C: AsyncI2c + ErrorType,
{
    /// Create a new BME280 struct using the primary I²C address `0x76`
    pub fn new_primary(i2c: I2C) -> Self {
        Self::new(i2c, BME280_I2C_ADDR_PRIMARY)
    }

    /// Create a new BME280 struct using the secondary I²C address `0x77`
    pub fn new_secondary(i2c: I2C) -> Self {
        Self::new(i2c, BME280_I2C_ADDR_SECONDARY)
    }

    /// Create a new BME280 struct using a custom I²C address
    pub fn new(i2c: I2C, address: u8) -> Self {
        Self {
            common: AsyncBME280Common {
                interface: I2CInterface { i2c, address },
                calibration: None,
            },
        }
    }

    /// Initializes the BME280.
    /// This configures 2x temperature oversampling, 16x pressure oversampling, and the IIR filter
    /// coefficient 16.
    pub async fn init<D: AsyncDelayNs>(&mut self, delay: &mut D) -> Result<(), Error<I2C::Error>> {
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
    ) -> Result<(), Error<I2C::Error>> {
        self.common.init(delay, config).await
    }

    /// Captures and processes sensor data for temperature, pressure, and humidity
    pub async fn measure<D: AsyncDelayNs>(
        &mut self,
        delay: &mut D,
    ) -> Result<Measurements<I2C::Error>, Error<I2C::Error>> {
        self.common.measure(delay).await
    }
}

/// Register access functions for I2C
#[derive(Debug, Default)]
struct I2CInterface<I2C> {
    /// concrete I²C device implementation
    i2c: I2C,
    /// I²C device address
    address: u8,
}

#[cfg(feature = "sync")]
impl<I2C> Interface for I2CInterface<I2C>
where
    I2C: I2c + ErrorType,
{
    type Error = I2C::Error;

    fn read_register(&mut self, register: u8) -> Result<u8, Error<I2C::Error>> {
        let mut data: [u8; 1] = [0];
        self.i2c
            .write_read(self.address, &[register], &mut data)
            .map_err(Error::Bus)?;
        Ok(data[0])
    }

    fn read_data(
        &mut self,
        register: u8,
    ) -> Result<[u8; BME280_P_T_H_DATA_LEN], Error<I2C::Error>> {
        let mut data = [0; BME280_P_T_H_DATA_LEN];
        self.i2c
            .write_read(self.address, &[register], &mut data)
            .map_err(Error::Bus)?;
        Ok(data)
    }

    fn read_pt_calib_data(
        &mut self,
        register: u8,
    ) -> Result<[u8; BME280_P_T_CALIB_DATA_LEN], Error<I2C::Error>> {
        let mut data = [0; BME280_P_T_CALIB_DATA_LEN];
        self.i2c
            .write_read(self.address, &[register], &mut data)
            .map_err(Error::Bus)?;
        Ok(data)
    }

    fn read_h_calib_data(
        &mut self,
        register: u8,
    ) -> Result<[u8; BME280_H_CALIB_DATA_LEN], Error<I2C::Error>> {
        let mut data = [0; BME280_H_CALIB_DATA_LEN];
        self.i2c
            .write_read(self.address, &[register], &mut data)
            .map_err(Error::Bus)?;
        Ok(data)
    }

    fn write_register(&mut self, register: u8, payload: u8) -> Result<(), Error<I2C::Error>> {
        self.i2c
            .write(self.address, &[register, payload])
            .map_err(Error::Bus)
    }
}

#[cfg(feature = "async")]
impl<I2C> AsyncInterface for I2CInterface<I2C>
where
    I2C: AsyncI2c + ErrorType,
{
    type Error = I2C::Error;

    type ReadRegisterFuture<'a> = impl Future<Output = Result<u8, Error<Self::Error>>>
    where
        I2C: 'a;
    fn read_register(&mut self, register: u8) -> Self::ReadRegisterFuture<'_> {
        async move {
            let mut data: [u8; 1] = [0];
            self.i2c
                .write_read(self.address, &[register], &mut data)
                .await
                .map_err(Error::Bus)?;
            Ok(data[0])
        }
    }

    type ReadDataFuture<'a> = impl Future<Output = Result<[u8; BME280_P_T_H_DATA_LEN], Error<Self::Error>>>
    where
        I2C: 'a;
    fn read_data(&mut self, register: u8) -> Self::ReadDataFuture<'_> {
        async move {
            let mut data = [0; BME280_P_T_H_DATA_LEN];
            self.i2c
                .write_read(self.address, &[register], &mut data)
                .await
                .map_err(Error::Bus)?;
            Ok(data)
        }
    }

    type ReadPtCalibDataFuture<'a> = impl Future<Output = Result<[u8; BME280_P_T_CALIB_DATA_LEN], Error<Self::Error>>>
    where
        I2C: 'a;
    fn read_pt_calib_data(&mut self, register: u8) -> Self::ReadPtCalibDataFuture<'_> {
        async move {
            let mut data = [0; BME280_P_T_CALIB_DATA_LEN];
            self.i2c
                .write_read(self.address, &[register], &mut data)
                .await
                .map_err(Error::Bus)?;
            Ok(data)
        }
    }

    type ReadHCalibDataFuture<'a> = impl Future<Output = Result<[u8; BME280_H_CALIB_DATA_LEN], Error<Self::Error>>>
    where
        I2C: 'a;
    fn read_h_calib_data(&mut self, register: u8) -> Self::ReadHCalibDataFuture<'_> {
        async move {
            let mut data = [0; BME280_H_CALIB_DATA_LEN];
            self.i2c
                .write_read(self.address, &[register], &mut data)
                .await
                .map_err(Error::Bus)?;
            Ok(data)
        }
    }

    type WriteRegisterFuture<'a> = impl Future<Output = Result<(), Error<Self::Error>>>
    where
        I2C: 'a;
    fn write_register(&mut self, register: u8, payload: u8) -> Self::WriteRegisterFuture<'_> {
        async move {
            self.i2c
                .write(self.address, &[register, payload])
                .await
                .map_err(Error::Bus)
        }
    }
}
