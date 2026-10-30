#![doc(html_root_url = "https://docs.rs/bme280")]
#![doc(issue_tracker_base_url = "https://github.com/VersBinarii/bme280/issues/")]
#![deny(
    missing_docs,
    missing_debug_implementations,
    missing_copy_implementations,
    trivial_casts,
    trivial_numeric_casts,
    unsafe_code,
    unused_import_braces,
    unused_qualifications,
    unused_variables,
    unreachable_code,
    unused_comparisons,
    unused_imports,
    unused_must_use
)]
#![cfg_attr(not(feature = "async"), deny(unstable_features))]
// Turn off no_std if we turn on the "with_std" feature
#![cfg_attr(not(feature = "with_std"), no_std)]
#![cfg_attr(
    feature = "async",
    feature(type_alias_impl_trait),
    feature(impl_trait_in_assoc_type)
)]

//! A platform agnostic Rust driver for the Bosch BME280 and BMP280, based on the
//! [`embedded-hal`](https://github.com/rust-embedded/embedded-hal) traits.
//!
//! ## The Device
//!
//! The [Bosch BME280](https://www.bosch-sensortec.com/bst/products/all_products/bme280)
//! is a highly accurate sensor for atmospheric temperature, pressure, and
//! relative humidity.
//!
//! The [Bosch BMP280](https://www.bosch-sensortec.com/bst/products/all_products/bmp280)
//! is a highly accurate sensor for atmospheric temperature, and pressure.
//!
//! The device has I²C and SPI interfaces.
//!
//! ## Usage
//!
//! ```no_run
//! use linux_embedded_hal::{Delay, I2cdev};
//! use bme280::i2c::BME280;
//!
//! // using Linux I2C Bus #1 in this example
//! let i2c_bus = I2cdev::new("/dev/i2c-1").unwrap();
//!
//! // initialize the BME280 using the primary I2C address 0x76
//! let mut bme280 = BME280::new_primary(i2c_bus, Delay);
//!
//! // or, initialize the BME280 using the secondary I2C address 0x77
//! // let mut bme280 = BME280::new_secondary(i2c_bus, Delay);
//!
//! // or, initialize the BME280 using a custom I2C address
//! // let bme280_i2c_addr = 0x88;
//! // let mut bme280 = BME280::new(i2c_bus, bme280_i2c_addr, Delay);
//!
//! // initialize the sensor
//! bme280.init().unwrap();
//!
//! // measure temperature, pressure, and humidity
//! let measurements = bme280.measure().unwrap();
//!
//! println!("Relative Humidity = {}%", measurements.humidity);
//! println!("Temperature = {} deg C", measurements.temperature);
//! println!("Pressure = {} pascals", measurements.pressure);
//! ```

pub mod i2c;
pub mod spi;

#[cfg(feature = "async")]
use core::future::Future;
use core::marker::PhantomData;
#[cfg(feature = "sync")]
use embedded_hal::delay::DelayNs;
#[cfg(feature = "async")]
use embedded_hal_async::delay::DelayNs as AsyncDelayNs;

#[cfg(feature = "serde")]
use serde::Serialize;

#[cfg(feature = "with_defmt")]
use defmt::{write, Format, Formatter};

#[cfg(feature = "with_std")]
use derive_more::Display;
#[cfg(feature = "with_std")]
use std::error;
#[cfg(feature = "with_std")]
use std::fmt;

const BME280_PWR_CTRL_ADDR: u8 = 0xF4;
const BME280_CTRL_HUM_ADDR: u8 = 0xF2;
const BME280_CTRL_MEAS_ADDR: u8 = 0xF4;
const BME280_CONFIG_ADDR: u8 = 0xF5;

const BME280_RESET_ADDR: u8 = 0xE0;
const BME280_SOFT_RESET_CMD: u8 = 0xB6;

const BME280_CHIP_ID: u8 = 0x60;
const BMP280_CHIP_ID: u8 = 0x58;
const BME280_CHIP_ID_ADDR: u8 = 0xD0;

const BME280_DATA_ADDR: u8 = 0xF7;
const BME280_P_T_H_DATA_LEN: usize = 8;

const BME280_P_T_CALIB_DATA_ADDR: u8 = 0x88;
const BME280_P_T_CALIB_DATA_LEN: usize = 26;

const BME280_H_CALIB_DATA_ADDR: u8 = 0xE1;
const BME280_H_CALIB_DATA_LEN: usize = 7;

const BME280_TEMP_MIN: f32 = -40.0;
const BME280_TEMP_MAX: f32 = 85.0;

const BME280_PRESSURE_MIN: f32 = 30000.0;
const BME280_PRESSURE_MAX: f32 = 110000.0;

const BME280_HUMIDITY_MIN: f32 = 0.0;
const BME280_HUMIDITY_MAX: f32 = 100.0;

const BME280_SLEEP_MODE: u8 = 0x00;
const BME280_FORCED_MODE: u8 = 0x01;
const BME280_NORMAL_MODE: u8 = 0x03;

const BME280_SENSOR_MODE_MSK: u8 = 0x03;

const BME280_CTRL_HUM_MSK: u8 = 0x07;

const BME280_CTRL_PRESS_MSK: u8 = 0x1C;
const BME280_CTRL_PRESS_POS: u8 = 0x02;

const BME280_CTRL_TEMP_MSK: u8 = 0xE0;
const BME280_CTRL_TEMP_POS: u8 = 0x05;

const BME280_FILTER_MSK: u8 = 0x1C;
const BME280_FILTER_POS: u8 = 0x02;
const BME280_FILTER_COEFF_OFF: u8 = 0x00;
const BME280_FILTER_COEFF_2: u8 = 0x01;
const BME280_FILTER_COEFF_4: u8 = 0x02;
const BME280_FILTER_COEFF_8: u8 = 0x03;
const BME280_FILTER_COEFF_16: u8 = 0x04;

const BME280_OVERSAMPLING_1X: u8 = 0x01;
const BME280_OVERSAMPLING_2X: u8 = 0x02;
const BME280_OVERSAMPLING_4X: u8 = 0x03;
const BME280_OVERSAMPLING_8X: u8 = 0x04;
const BME280_OVERSAMPLING_16X: u8 = 0x05;

macro_rules! concat_bytes {
    ($msb:expr, $lsb:expr) => {
        (($msb as u16) << 8) | ($lsb as u16)
    };
}

macro_rules! set_bits {
    ($reg_data:expr, $mask:expr, $pos:expr, $data:expr) => {
        ($reg_data & !$mask) | (($data << $pos) & $mask)
    };
}

/// BME280 errors
#[cfg_attr(feature = "with_std", derive(Display))]
#[derive(Debug)]
pub enum Error<E> {
    /// Failed to compensate a raw measurement
    CompensationFailed,
    /// I²C or SPI bus error
    Bus(E),
    /// Failed to parse sensor data
    InvalidData,
    /// No calibration data is available (probably forgot to call or check BME280::init for failure)
    NoCalibrationData,
    /// Chip ID doesn't match expected value
    UnsupportedChip,
    /// Delay error
    Delay,
}

#[cfg(feature = "with_defmt")]
impl<E> Format for Error<E> {
    fn format(&self, fmt: Formatter) {
        match self {
            Error::CompensationFailed => write!(fmt, "Compensation failure"),
            Error::Bus(_) => write!(fmt, "Bus error"),
            Error::InvalidData => write!(fmt, "Invalid data"),
            Error::NoCalibrationData => write!(fmt, "No calibration data"),
            Error::UnsupportedChip => write!(fmt, "Unsupported chip"),
            Error::Delay => write!(fmt, "Delay issue"),
        }
    }
}

#[cfg(feature = "with_std")]
impl<T: fmt::Debug + fmt::Display> error::Error for Error<T> {}

/// BME280 operating mode
#[derive(Debug, Copy, Clone)]
#[cfg_attr(feature = "with_defmt", derive(defmt::Format))]
pub enum SensorMode {
    /// Sleep mode
    Sleep,
    /// Forced mode
    Forced,
    /// Normal mode
    Normal,
}

/// Oversampling settings for temperature, pressure, and humidity measurements.
/// See sections 3.4ff of the manual for measurement flow and recommended values.
/// The default is 1x, i.e., no oversampling.
#[derive(Debug, Copy, Clone)]
#[cfg_attr(feature = "with_defmt", derive(defmt::Format))]
pub enum Oversampling {
    /// Disables oversampling.
    /// Without IIR filtering, this sets the resolution of temperature and pressure measurements
    /// to 16 bits.
    Oversampling1X,
    /// Configures 2x oversampling.
    /// This increases the resolution of temperature and pressure measurements to 17 bits without
    /// IIR filtering.
    Oversampling2X,
    /// Configures 4x oversampling.
    /// This increases the resolution of temperature and pressure measurements to 18 bits without
    /// IIR filtering.
    Oversampling4X,
    /// Configures 8x oversampling.
    /// This increases the resolution of temperature and pressure measurements to 19 bits without
    /// IIR filtering.
    Oversampling8X,
    /// Configures 16x oversampling.
    /// This increases the resolution of temperature and pressure measurements to 20 bits,
    /// regardless of IIR filtering.
    Oversampling16X,
}

impl Oversampling {
    fn bits(&self) -> u8 {
        match self {
            Oversampling::Oversampling1X => BME280_OVERSAMPLING_1X,
            Oversampling::Oversampling2X => BME280_OVERSAMPLING_2X,
            Oversampling::Oversampling4X => BME280_OVERSAMPLING_4X,
            Oversampling::Oversampling8X => BME280_OVERSAMPLING_8X,
            Oversampling::Oversampling16X => BME280_OVERSAMPLING_16X,
        }
    }
}

impl Default for Oversampling {
    fn default() -> Self {
        Self::Oversampling1X
    }
}

/// Lowpass filter settings for pressure and temperature values.
/// See section 3.4.4 of the datasheet for more information on this.
/// The default setting is disabled.
#[derive(Debug, Copy, Clone, Default)]
#[cfg_attr(feature = "with_defmt", derive(defmt::Format))]
pub enum IIRFilter {
    /// Disables the IIR filter.
    /// The resolution of pressure and temperature measurements is dictated by their respective
    /// oversampling settings.
    #[default]
    Off,

    /// Sets the IIR filter coefficient to 2.
    /// This increases the resolution of the pressure and temperature measurements to 20 bits.
    /// See sections 3.4.4 and 3.5 of the datasheet for more information.
    Coefficient2,

    /// Sets the IIR filter coefficient to 4.
    Coefficient4,

    /// Sets the IIR filter coefficient to 8.
    Coefficient8,

    /// Sets the IIR filter coefficient to 16.
    Coefficient16,
}

impl IIRFilter {
    fn bits(&self) -> u8 {
        match self {
            IIRFilter::Off => BME280_FILTER_COEFF_OFF,
            IIRFilter::Coefficient2 => BME280_FILTER_COEFF_2,
            IIRFilter::Coefficient4 => BME280_FILTER_COEFF_4,
            IIRFilter::Coefficient8 => BME280_FILTER_COEFF_8,
            IIRFilter::Coefficient16 => BME280_FILTER_COEFF_16,
        }
    }
}

/// Configuration values for the BME280 sensor.
/// The default sets all oversampling settings to 1x and disables the IIR filter.
#[derive(Debug, Copy, Clone, Default)]
#[cfg_attr(feature = "with_defmt", derive(defmt::Format))]
pub struct Configuration {
    temperature_oversampling: Oversampling,
    pressure_oversampling: Oversampling,
    humidity_oversampling: Oversampling,
    iir_filter: IIRFilter,
}

impl Configuration {
    /// Sets the temperature oversampling setting.
    pub fn with_temperature_oversampling(mut self, oversampling: Oversampling) -> Self {
        self.temperature_oversampling = oversampling;
        self
    }

    /// Sets the pressure oversampling setting.
    pub fn with_pressure_oversampling(mut self, oversampling: Oversampling) -> Self {
        self.pressure_oversampling = oversampling;
        self
    }

    /// Sets the humidity oversampling setting
    pub fn with_humidity_oversampling(mut self, oversampling: Oversampling) -> Self {
        self.humidity_oversampling = oversampling;
        self
    }

    /// Sets the IIR filter setting.
    pub fn with_iir_filter(mut self, filter: IIRFilter) -> Self {
        self.iir_filter = filter;
        self
    }
}

#[derive(Debug)]
#[cfg_attr(feature = "with_defmt", derive(defmt::Format))]
struct CalibrationData {
    dig_t1: u16,
    dig_t2: i16,
    dig_t3: i16,
    dig_p1: u16,
    dig_p2: i16,
    dig_p3: i16,
    dig_p4: i16,
    dig_p5: i16,
    dig_p6: i16,
    dig_p7: i16,
    dig_p8: i16,
    dig_p9: i16,
    dig_h1: u8,
    dig_h2: i16,
    dig_h3: u8,
    dig_h4: i16,
    dig_h5: i16,
    dig_h6: i8,
    t_fine: i32,
}

/// Measurement data
#[cfg_attr(feature = "serde", derive(Serialize))]
#[cfg_attr(feature = "with_defmt", derive(defmt::Format))]
#[derive(Debug)]
pub struct Measurements<E> {
    /// temperature in degrees celsius
    pub temperature: f32,
    /// pressure in pascals
    pub pressure: f32,
    /// percent relative humidity (`0` with BMP280)
    pub humidity: f32,
    #[cfg_attr(feature = "serde", serde(skip))]
    _e: PhantomData<E>,
}

impl<E> Measurements<E> {
    fn parse(
        data: [u8; BME280_P_T_H_DATA_LEN],
        calibration: &mut CalibrationData,
    ) -> Result<Self, Error<E>> {
        let data_msb = (data[0] as u32) << 12;
        let data_lsb = (data[1] as u32) << 4;
        let data_xlsb = (data[2] as u32) >> 4;
        let pressure = data_msb | data_lsb | data_xlsb;

        let data_msb = (data[3] as u32) << 12;
        let data_lsb = (data[4] as u32) << 4;
        let data_xlsb = (data[5] as u32) >> 4;
        let temperature = data_msb | data_lsb | data_xlsb;

        let data_msb = (data[6] as u32) << 8;
        let data_lsb = data[7] as u32;
        let humidity = data_msb | data_lsb;

        let temperature = Measurements::compensate_temperature(temperature, calibration)?;
        let pressure = Measurements::compensate_pressure(pressure, calibration)?;
        let humidity = Measurements::compensate_humidity(humidity, calibration)?;

        Ok(Measurements {
            temperature,
            pressure,
            humidity,
            _e: PhantomData,
        })
    }

    fn compensate_temperature(
        uncompensated: u32,
        calibration: &mut CalibrationData,
    ) -> Result<f32, Error<E>> {
        let var1 = uncompensated as f32 / 16384.0 - calibration.dig_t1 as f32 / 1024.0;
        let var1 = var1 * calibration.dig_t2 as f32;
        let var2 = uncompensated as f32 / 131072.0 - calibration.dig_t1 as f32 / 8192.0;
        let var2 = var2 * var2 * calibration.dig_t3 as f32;

        calibration.t_fine = (var1 + var2) as i32;

        let temperature = (var1 + var2) / 5120.0;
        let temperature = if temperature < BME280_TEMP_MIN {
            BME280_TEMP_MIN
        } else if temperature > BME280_TEMP_MAX {
            BME280_TEMP_MAX
        } else {
            temperature
        };
        Ok(temperature)
    }

    fn compensate_pressure(
        uncompensated: u32,
        calibration: &mut CalibrationData,
    ) -> Result<f32, Error<E>> {
        let var1 = calibration.t_fine as f32 / 2.0 - 64000.0;
        let var2 = var1 * var1 * calibration.dig_p6 as f32 / 32768.0;
        let var2 = var2 + var1 * calibration.dig_p5 as f32 * 2.0;
        let var2 = var2 / 4.0 + calibration.dig_p4 as f32 * 65536.0;
        let var3 = calibration.dig_p3 as f32 * var1 * var1 / 524288.0;
        let var1 = (var3 + calibration.dig_p2 as f32 * var1) / 524288.0;
        let var1 = (1.0 + var1 / 32768.0) * calibration.dig_p1 as f32;

        let pressure = if var1 > 0.0 {
            let pressure = 1048576.0 - uncompensated as f32;
            let pressure = (pressure - (var2 / 4096.0)) * 6250.0 / var1;
            let var1 = calibration.dig_p9 as f32 * pressure * pressure / 2147483648.0;
            let var2 = pressure * calibration.dig_p8 as f32 / 32768.0;
            let pressure = pressure + (var1 + var2 + calibration.dig_p7 as f32) / 16.0;
            if pressure < BME280_PRESSURE_MIN {
                BME280_PRESSURE_MIN
            } else if pressure > BME280_PRESSURE_MAX {
                BME280_PRESSURE_MAX
            } else {
                pressure
            }
        } else {
            return Err(Error::InvalidData);
        };
        Ok(pressure)
    }

    fn compensate_humidity(
        uncompensated: u32,
        calibration: &mut CalibrationData,
    ) -> Result<f32, Error<E>> {
        let var1 = calibration.t_fine as f32 - 76800.0;
        let var2 = calibration.dig_h4 as f32 * 64.0 + (calibration.dig_h5 as f32 / 16384.0) * var1;
        let var3 = uncompensated as f32 - var2;
        let var4 = calibration.dig_h2 as f32 / 65536.0;
        let var5 = 1.0 + (calibration.dig_h3 as f32 / 67108864.0) * var1;
        let var6 = 1.0 + (calibration.dig_h6 as f32 / 67108864.0) * var1 * var5;
        let var6 = var3 * var4 * (var5 * var6);

        let humidity = var6 * (1.0 - calibration.dig_h1 as f32 * var6 / 524288.0);
        let humidity = if humidity < BME280_HUMIDITY_MIN {
            BME280_HUMIDITY_MIN
        } else if humidity > BME280_HUMIDITY_MAX {
            BME280_HUMIDITY_MAX
        } else {
            humidity
        };
        Ok(humidity)
    }
}

trait Interface {
    type Error;

    fn read_register(&mut self, register: u8) -> Result<u8, Error<Self::Error>>;

    fn read_data(
        &mut self,
        register: u8,
    ) -> Result<[u8; BME280_P_T_H_DATA_LEN], Error<Self::Error>>;

    fn read_pt_calib_data(
        &mut self,
        register: u8,
    ) -> Result<[u8; BME280_P_T_CALIB_DATA_LEN], Error<Self::Error>>;

    fn read_h_calib_data(
        &mut self,
        register: u8,
    ) -> Result<[u8; BME280_H_CALIB_DATA_LEN], Error<Self::Error>>;

    fn write_register(&mut self, register: u8, payload: u8) -> Result<(), Error<Self::Error>>;
}

#[cfg(feature = "async")]
trait AsyncInterface {
    type Error;

    type ReadRegisterFuture<'a>: Future<Output = Result<u8, Error<Self::Error>>>
    where
        Self: 'a;
    fn read_register(&mut self, register: u8) -> Self::ReadRegisterFuture<'_>;

    type ReadDataFuture<'a>: Future<
        Output = Result<[u8; BME280_P_T_H_DATA_LEN], Error<Self::Error>>,
    >
    where
        Self: 'a;
    fn read_data(&mut self, register: u8) -> Self::ReadDataFuture<'_>;

    type ReadPtCalibDataFuture<'a>: Future<
        Output = Result<[u8; BME280_P_T_CALIB_DATA_LEN], Error<Self::Error>>,
    >
    where
        Self: 'a;
    fn read_pt_calib_data(&mut self, register: u8) -> Self::ReadPtCalibDataFuture<'_>;

    type ReadHCalibDataFuture<'a>: Future<
        Output = Result<[u8; BME280_H_CALIB_DATA_LEN], Error<Self::Error>>,
    >
    where
        Self: 'a;
    fn read_h_calib_data(&mut self, register: u8) -> Self::ReadHCalibDataFuture<'_>;

    type WriteRegisterFuture<'a>: Future<Output = Result<(), Error<Self::Error>>>
    where
        Self: 'a;
    fn write_register(&mut self, register: u8, payload: u8) -> Self::WriteRegisterFuture<'_>;
}

/// Common driver code for I2C and SPI interfaces
#[maybe_async_cfg::maybe(
    sync(feature = "sync", self = "BME280Common"),
    async(feature = "async", keep_self)
)]
#[derive(Debug, Default)]
struct AsyncBME280Common<I> {
    /// Interface to the chip (either I2C or SPI)
    interface: I,
    /// calibration data
    calibration: Option<CalibrationData>,
}

#[maybe_async_cfg::maybe(
    sync(
        feature = "sync",
        self = "BME280Common",
        idents(AsyncInterface(sync = "Interface"), AsyncDelayNs(sync = "DelayNs"),)
    ),
    async(feature = "async", keep_self)
)]
impl<I> AsyncBME280Common<I>
where
    I: AsyncInterface,
{
    /// Initializes the BME280, applying the given config.
    async fn init<D: AsyncDelayNs>(
        &mut self,
        delay: &mut D,
        config: Configuration,
    ) -> Result<(), Error<I::Error>> {
        self.verify_chip_id().await?;
        self.soft_reset(delay).await?;
        self.calibrate().await?;
        self.configure(delay, config).await
    }

    async fn verify_chip_id(&mut self) -> Result<(), Error<I::Error>> {
        let chip_id = self.interface.read_register(BME280_CHIP_ID_ADDR).await?;
        if chip_id == BME280_CHIP_ID || chip_id == BMP280_CHIP_ID {
            Ok(())
        } else {
            Err(Error::UnsupportedChip)
        }
    }

    async fn soft_reset<D: AsyncDelayNs>(&mut self, delay: &mut D) -> Result<(), Error<I::Error>> {
        self.interface
            .write_register(BME280_RESET_ADDR, BME280_SOFT_RESET_CMD)
            .await?;
        delay.delay_ms(2).await; // startup time is 2ms
        Ok(())
    }

    async fn calibrate(&mut self) -> Result<(), Error<I::Error>> {
        let pt_calib_data = self
            .interface
            .read_pt_calib_data(BME280_P_T_CALIB_DATA_ADDR)
            .await?;
        let h_calib_data = self
            .interface
            .read_h_calib_data(BME280_H_CALIB_DATA_ADDR)
            .await?;
        self.calibration = Some(parse_calib_data(&pt_calib_data, &h_calib_data));
        Ok(())
    }

    async fn configure<D: AsyncDelayNs>(
        &mut self,
        delay: &mut D,
        config: Configuration,
    ) -> Result<(), Error<I::Error>> {
        match self.mode().await? {
            SensorMode::Sleep => {}
            _ => self.soft_reset(delay).await?,
        };

        self.interface
            .write_register(
                BME280_CTRL_HUM_ADDR,
                config.humidity_oversampling.bits() & BME280_CTRL_HUM_MSK,
            )
            .await?;

        // As per the datasheet, the ctrl_meas register needs to be written after
        // the ctrl_hum register for changes to take effect.
        let data = self.interface.read_register(BME280_CTRL_MEAS_ADDR).await?;
        let data = set_bits!(
            data,
            BME280_CTRL_PRESS_MSK,
            BME280_CTRL_PRESS_POS,
            config.pressure_oversampling.bits()
        );
        let data = set_bits!(
            data,
            BME280_CTRL_TEMP_MSK,
            BME280_CTRL_TEMP_POS,
            config.temperature_oversampling.bits()
        );
        self.interface
            .write_register(BME280_CTRL_MEAS_ADDR, data)
            .await?;

        let data = self.interface.read_register(BME280_CONFIG_ADDR).await?;
        let data = set_bits!(
            data,
            BME280_FILTER_MSK,
            BME280_FILTER_POS,
            config.iir_filter.bits()
        );
        self.interface
            .write_register(BME280_CONFIG_ADDR, data)
            .await
    }

    async fn mode(&mut self) -> Result<SensorMode, Error<I::Error>> {
        let data = self.interface.read_register(BME280_PWR_CTRL_ADDR).await?;
        match data & BME280_SENSOR_MODE_MSK {
            BME280_SLEEP_MODE => Ok(SensorMode::Sleep),
            BME280_FORCED_MODE => Ok(SensorMode::Forced),
            BME280_NORMAL_MODE => Ok(SensorMode::Normal),
            _ => Err(Error::InvalidData),
        }
    }

    async fn forced<D: AsyncDelayNs>(&mut self, delay: &mut D) -> Result<(), Error<I::Error>> {
        self.set_mode(BME280_FORCED_MODE, delay).await
    }

    async fn set_mode<D: AsyncDelayNs>(
        &mut self,
        mode: u8,
        delay: &mut D,
    ) -> Result<(), Error<I::Error>> {
        match self.mode().await? {
            SensorMode::Sleep => {}
            _ => self.soft_reset(delay).await?,
        };
        let data = self.interface.read_register(BME280_PWR_CTRL_ADDR).await?;
        let data = set_bits!(data, BME280_SENSOR_MODE_MSK, 0, mode);
        self.interface
            .write_register(BME280_PWR_CTRL_ADDR, data)
            .await
    }

    /// Captures and processes sensor data for temperature, pressure, and humidity
    async fn measure<D: AsyncDelayNs>(
        &mut self,
        delay: &mut D,
    ) -> Result<Measurements<I::Error>, Error<I::Error>> {
        self.forced(delay).await?;
        delay.delay_ms(40).await;
        let measurements = self.interface.read_data(BME280_DATA_ADDR).await?;
        match self.calibration.as_mut() {
            Some(calibration) => {
                let measurements = Measurements::parse(measurements, &mut *calibration)?;
                Ok(measurements)
            }
            None => Err(Error::NoCalibrationData),
        }
    }
}

fn parse_calib_data(
    pt_data: &[u8; BME280_P_T_CALIB_DATA_LEN],
    h_data: &[u8; BME280_H_CALIB_DATA_LEN],
) -> CalibrationData {
    let dig_t1 = concat_bytes!(pt_data[1], pt_data[0]);
    let dig_t2 = concat_bytes!(pt_data[3], pt_data[2]) as i16;
    let dig_t3 = concat_bytes!(pt_data[5], pt_data[4]) as i16;
    let dig_p1 = concat_bytes!(pt_data[7], pt_data[6]);
    let dig_p2 = concat_bytes!(pt_data[9], pt_data[8]) as i16;
    let dig_p3 = concat_bytes!(pt_data[11], pt_data[10]) as i16;
    let dig_p4 = concat_bytes!(pt_data[13], pt_data[12]) as i16;
    let dig_p5 = concat_bytes!(pt_data[15], pt_data[14]) as i16;
    let dig_p6 = concat_bytes!(pt_data[17], pt_data[16]) as i16;
    let dig_p7 = concat_bytes!(pt_data[19], pt_data[18]) as i16;
    let dig_p8 = concat_bytes!(pt_data[21], pt_data[20]) as i16;
    let dig_p9 = concat_bytes!(pt_data[23], pt_data[22]) as i16;
    let dig_h1 = pt_data[25];
    let dig_h2 = concat_bytes!(h_data[1], h_data[0]) as i16;
    let dig_h3 = h_data[2];
    let dig_h4 = (h_data[3] as i8 as i16 * 16) | ((h_data[4] as i8 as i16) & 0x0F);
    let dig_h5 = (h_data[5] as i8 as i16 * 16) | (((h_data[4] as i8 as i16) & 0xF0) >> 4);
    let dig_h6 = h_data[6] as i8;

    CalibrationData {
        dig_t1,
        dig_t2,
        dig_t3,
        dig_p1,
        dig_p2,
        dig_p3,
        dig_p4,
        dig_p5,
        dig_p6,
        dig_p7,
        dig_p8,
        dig_p9,
        dig_h1,
        dig_h2,
        dig_h3,
        dig_h4,
        dig_h5,
        dig_h6,
        t_fine: 0,
    }
}
