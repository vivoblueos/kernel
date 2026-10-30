//! A platform agnostic driver to interface with the MAX7219 (LED matrix display driver)
//!
//! This driver was built using [`embedded-hal`] traits.
//!
//! [`embedded-hal`]: https://docs.rs/embedded-hal/~0.2

#![deny(unsafe_code)]
#![deny(warnings)]
#![no_std]

use embedded_hal::digital::OutputPin;
use embedded_hal::spi::SpiDevice;

pub mod connectors;
use connectors::*;

/// Maximum number of displays connected in series supported by this lib.
const MAX_DISPLAYS: usize = 8;

/// Digits per display
const MAX_DIGITS: usize = 8;

/// Possible command register values on the display chip.
#[derive(Clone, Copy)]
pub enum Command {
    Noop = 0x00,
    Digit0 = 0x01,
    Digit1 = 0x02,
    Digit2 = 0x03,
    Digit3 = 0x04,
    Digit4 = 0x05,
    Digit5 = 0x06,
    Digit6 = 0x07,
    Digit7 = 0x08,
    DecodeMode = 0x09,
    Intensity = 0x0A,
    ScanLimit = 0x0B,
    Power = 0x0C,
    DisplayTest = 0x0F,
}

/// Decode modes for BCD encoded input.
#[derive(Copy, Clone)]
pub enum DecodeMode {
    NoDecode = 0x00,
    CodeBDigit0 = 0x01,
    CodeBDigits3_0 = 0x0F,
    CodeBDigits7_0 = 0xFF,
}

///
/// Error raised in case there was an error
/// during communication with the MAX7219 chip.
///
#[derive(Debug)]
pub enum DataError {
    /// An error occurred when working with SPI
    Spi,
    /// An error occurred when working with a PIN
    Pin,
}

///
/// Handles communication with the MAX7219
/// chip for segmented displays. Each display can be
/// connected in series with another and controlled via
/// a single connection. The actual connection interface
/// is selected via constructor functions.
///
pub struct MAX7219<CONNECTOR> {
    c: CONNECTOR,
    decode_mode: DecodeMode,
}

impl<CONNECTOR> MAX7219<CONNECTOR>
where
    CONNECTOR: Connector,
{
    ///
    /// Powers on all connected displays
    ///
    /// # Errors
    ///
    /// * `DataError` - returned in case there was an error during data transfer
    ///
    pub fn power_on(&mut self) -> Result<(), DataError> {
        for i in 0..self.c.devices() {
            self.c.write_data(i, Command::Power, 0x01)?;
        }

        Ok(())
    }

    ///
    /// Powers off all connected displays
    ///
    /// # Errors
    ///
    /// * `DataError` - returned in case there was an error during data transfer
    ///
    pub fn power_off(&mut self) -> Result<(), DataError> {
        for i in 0..self.c.devices() {
            self.c.write_data(i, Command::Power, 0x00)?;
        }

        Ok(())
    }

    ///
    /// Clears display by settings all digits to empty
    ///
    /// # Arguments
    ///
    /// * `addr` - display to address as connected in series (0 -> last)
    ///
    /// # Errors
    ///
    /// * `DataError` - returned in case there was an error during data transfer
    ///
    pub fn clear_display(&mut self, addr: usize) -> Result<(), DataError> {
        for i in 1..9 {
            self.c.write_raw(addr, i, 0x00)?;
        }

        Ok(())
    }

    ///
    /// Sets intensity level on the display
    ///
    /// # Arguments
    ///
    /// * `addr` - display to address as connected in series (0 -> last)
    /// * `intensity` - intensity value to set to `0x00` to 0x0F`
    ///
    /// # Errors
    ///
    /// * `DataError` - returned in case there was an error during data transfer
    ///
    pub fn set_intensity(&mut self, addr: usize, intensity: u8) -> Result<(), DataError> {
        self.c.write_data(addr, Command::Intensity, intensity)
    }

    ///
    /// Sets decode mode to be used on input sent to the display chip.
    ///
    /// # Arguments
    ///
    /// * `addr` - display to address as connected in series (0 -> last)
    /// * `mode` - the decode mode to set
    ///
    /// # Errors
    ///
    /// * `DataError` - returned in case there was an error during data transfer
    ///
    pub fn set_decode_mode(&mut self, addr: usize, mode: DecodeMode) -> Result<(), DataError> {
        self.decode_mode = mode; // store what we set
        self.c.write_data(addr, Command::DecodeMode, mode as u8)
    }

    ///
    /// Writes byte string to the display
    ///
    /// # Arguments
    ///
    /// * `addr` - display to address as connected in series (0 -> last)
    /// * `string` - the byte string to send 8 bytes long. Unknown characters result in question mark.
    /// * `dots` - u8 bit array specifying where to put dots in the string (1 = dot, 0 = not)
    ///
    /// # Errors
    ///
    /// * `DataError` - returned in case there was an error during data transfer
    ///
    pub fn write_str(
        &mut self,
        addr: usize,
        string: &[u8; MAX_DIGITS],
        dots: u8,
    ) -> Result<(), DataError> {
        let prev_dm = self.decode_mode;
        self.set_decode_mode(0, DecodeMode::NoDecode)?;

        let mut digit: u8 = MAX_DIGITS as u8;
        let mut dot_product: u8 = 0b1000_0000;
        for b in string {
            let dot = (dots & dot_product) > 0;
            dot_product >>= 1;
            self.c.write_raw(addr, digit, ssb_byte(*b, dot))?;

            digit -= 1;
        }

        self.set_decode_mode(0, prev_dm)?;

        Ok(())
    }

    ///
    /// Writes BCD encoded string to the display
    ///
    /// # Arguments
    ///
    /// * `addr` - display to address as connected in series (0 -> last)
    /// * `bcd`  - the bcd encoded string slice consisting of [0-9,-,E,L,H,P]
    ///            where upper case input for alphabetic characters results in dot being set.
    ///            Length of string is always 8 bytes, use spaces for blanking.
    ///
    /// # Errors
    ///
    /// * `DataError` - returned in case there was an error during data transfer
    ///
    pub fn write_bcd(&mut self, addr: usize, bcd: &[u8; MAX_DIGITS]) -> Result<(), DataError> {
        let prev_dm = self.decode_mode;
        self.set_decode_mode(0, DecodeMode::CodeBDigits7_0)?;

        let mut digit: u8 = MAX_DIGITS as u8;
        for b in bcd {
            self.c.write_raw(addr, digit, bcd_byte(*b))?;

            digit -= 1;
        }

        self.set_decode_mode(0, prev_dm)?;

        Ok(())
    }

    ///
    /// Writes a right justified integer with sign
    ///
    /// # Arguments
    ///
    /// * `addr` - display to address as connected in series (0 -> last)
    /// * `val` - an integer i32
    ///
    /// # Errors
    ///
    /// * `DataError` - returned in case there was an integer over flow
    ///
    pub fn write_integer(&mut self, addr: usize, value: i32) -> Result<(), DataError> {
        let mut buf = [0u8; 8];
        let j = base_10_bytes(value, &mut buf);
        buf = pad_left(j);
        self.write_str(addr, &buf, 0b00000000)?;
        Ok(())
    }

    ///
    /// Writes a right justified hex formatted integer with sign
    ///
    /// # Arguments
    ///
    /// * `addr` - display to address as connected in series (0 -> last)
    /// * `val` - an integer i32
    ///
    /// # Errors
    ///
    /// * `DataError` - returned in case there was an integer over flow
    ///
    pub fn write_hex(&mut self, addr: usize, value: u32) -> Result<(), DataError> {
        let mut buf = [0u8; 8];
        let j = hex_bytes(value, &mut buf);
        buf = pad_left(j);
        self.write_str(addr, &buf, 0b00000000)?;
        Ok(())
    }

    ///
    /// Writes a raw value to the display
    ///
    /// # Arguments
    ///
    /// * `addr` - display to address as connected in series (0 -> last)
    /// * `raw` - an array of raw bytes to write. Each bit represents a pixel on the display
    ///
    /// # Errors
    ///
    /// * `DataError` - returned in case there was an error during data transfer
    ///
    pub fn write_raw(&mut self, addr: usize, raw: &[u8; MAX_DIGITS]) -> Result<(), DataError> {
        let prev_dm = self.decode_mode;
        self.set_decode_mode(0, DecodeMode::NoDecode)?;

        let mut digit: u8 = 1;
        for b in raw {
            self.write_raw_byte(addr, digit, *b)?;
            digit += 1;
        }

        self.set_decode_mode(0, prev_dm)?;

        Ok(())
    }

    ///
    /// Writes a single byte to the underlying display.  This method is very
    /// low-level: most users will prefer to use one of the other `write_*`
    /// methods.
    ///
    ///
    /// # Arguments
    ///
    /// * `addr` - display to address as connected in series (0 -> last)
    /// * `header` - the register to write the value to
    /// * `data` - the value to write
    ///
    /// # Errors
    ///
    /// * `DataError` - returned in case there was an error during data transfer
    ///
    pub fn write_raw_byte(&mut self, addr: usize, header: u8, data: u8) -> Result<(), DataError> {
        self.c.write_raw(addr, header, data)
    }

    ///
    /// Set test mode on/off
    ///
    /// # Arguments
    ///
    /// * `addr` - display to address as connected in series (0 -> last)
    /// * `is_on` - whether to turn test mode on or off
    ///
    /// # Errors
    ///
    /// * `DataError` - returned in case there was an error during data transfer
    ///
    pub fn test(&mut self, addr: usize, is_on: bool) -> Result<(), DataError> {
        if is_on {
            self.c.write_data(addr, Command::DisplayTest, 0x01)
        } else {
            self.c.write_data(addr, Command::DisplayTest, 0x00)
        }
    }

    // internal constructor, users should call ::from_pins or ::from_spi
    fn new(connector: CONNECTOR) -> Result<Self, DataError> {
        let mut max7219 = MAX7219 {
            c: connector,
            decode_mode: DecodeMode::NoDecode,
        };

        max7219.init()?;
        Ok(max7219)
    }

    fn init(&mut self) -> Result<(), DataError> {
        for i in 0..self.c.devices() {
            self.test(i, false)?; // turn testmode off
            self.c.write_data(i, Command::ScanLimit, 0x07)?; // set scanlimit
            self.set_decode_mode(i, DecodeMode::NoDecode)?; // direct decode
            self.clear_display(i)?; // clear all digits
        }
        self.power_off()?; // power off

        Ok(())
    }
}

impl<DATA, CS, SCK> MAX7219<PinConnector<DATA, CS, SCK>>
where
    DATA: OutputPin,
    CS: OutputPin,
    SCK: OutputPin,
{
    ///
    /// Construct a new MAX7219 driver instance from DATA, CS and SCK pins.
    ///
    /// # Arguments
    ///
    /// * `displays` - number of displays connected in series
    /// * `data` - the MOSI/DATA PIN used to send data through to the display set to output mode
    /// * `cs` - the CS PIN used to LOAD register on the display set to output mode
    /// * `sck` - the SCK clock PIN used to drive the clock set to output mode
    ///
    /// # Errors
    ///
    /// * `DataError` - returned in case there was an error during data transfer
    ///
    pub fn from_pins(displays: usize, data: DATA, cs: CS, sck: SCK) -> Result<Self, DataError> {
        MAX7219::new(PinConnector::new(displays, data, cs, sck))
    }
}

impl<SPI> MAX7219<SpiConnector<SPI>>
where
    SPI: SpiDevice<u8>,
{
    ///
    /// Construct a new MAX7219 driver instance from pre-existing SPI in full hardware mode.
    /// The SPI will control CS (LOAD) line according to it's internal mode set.
    /// If you need the CS line to be controlled manually use MAX7219::from_spi_cs
    ///
    /// * `NOTE` - make sure the SPI is initialized in MODE_0 with max 10 Mhz frequency.
    ///
    /// # Arguments
    ///
    /// * `displays` - number of displays connected in series
    /// * `spi` - the SPI interface initialized with MOSI, MISO(unused) and CLK
    ///
    /// # Errors
    ///
    /// * `DataError` - returned in case there was an error during data transfer
    ///
    pub fn from_spi(displays: usize, spi: SPI) -> Result<Self, DataError> {
        MAX7219::new(SpiConnector::new(displays, spi))
    }
}

impl<SPI, CS> MAX7219<SpiConnectorSW<SPI, CS>>
where
    SPI: SpiDevice<u8>,
    CS: OutputPin,
{
    ///
    /// Construct a new MAX7219 driver instance from pre-existing SPI and CS pin
    /// set to output. This version of the connection uses the CS pin manually
    /// to avoid issues with how the CS mode is handled in hardware SPI implementations.
    ///
    /// * `NOTE` - make sure the SPI is initialized in MODE_0 with max 10 Mhz frequency.
    ///
    /// # Arguments
    ///
    /// * `displays` - number of displays connected in series
    /// * `spi` - the SPI interface initialized with MOSI, MISO(unused) and CLK
    /// * `cs` - the CS PIN used to LOAD register on the display set to output mode
    ///
    /// # Errors
    ///
    /// * `DataError` - returned in case there was an error during data transfer
    ///
    pub fn from_spi_cs(displays: usize, spi: SPI, cs: CS) -> Result<Self, DataError> {
        MAX7219::new(SpiConnectorSW::new(displays, spi, cs))
    }
}

///
/// Translate alphanumeric ASCII bytes into BCD
/// encoded bytes expected by the display chip.
///
fn bcd_byte(b: u8) -> u8 {
    match b as char {
        ' ' => 0b0000_1111, // "blank"
        '-' => 0b0000_1010, // - without .
        'e' => 0b0000_1011, // E without .
        'E' => 0b1000_1011, // E with .
        'h' => 0b0000_1100, // H without .
        'H' => 0b1000_1100, // H with .
        'l' => 0b0000_1101, // L without .
        'L' => 0b1000_1101, // L with .
        'p' => 0b0000_1110, // L without .
        'P' => 0b1000_1110, // L with .
        _ => b,
    }
}

///
/// Translate alphanumeric ASCII bytes into segment set bytes
///
fn ssb_byte(b: u8, dot: bool) -> u8 {
    let mut result = match b as char {
        ' ' => 0b0000_0000, // "blank"
        '.' => 0b1000_0000,
        '-' => 0b0000_0001, // -
        '_' => 0b0000_1000, // _
        '0' => 0b0111_1110,
        '1' => 0b0011_0000,
        '2' => 0b0110_1101,
        '3' => 0b0111_1001,
        '4' => 0b0011_0011,
        '5' => 0b0101_1011,
        '6' => 0b0101_1111,
        '7' => 0b0111_0000,
        '8' => 0b0111_1111,
        '9' => 0b0111_1011,
        'a' | 'A' => 0b0111_0111,
        'b' => 0b0001_1111,
        'c' | 'C' => 0b0100_1110,
        'd' => 0b0011_1101,
        'e' | 'E' => 0b0100_1111,
        'f' | 'F' => 0b0100_0111,
        'g' | 'G' => 0b0101_1110,
        'h' | 'H' => 0b0011_0111,
        'i' | 'I' => 0b0011_0000,
        'j' | 'J' => 0b0011_1100,
        // K undoable
        'l' | 'L' => 0b0000_1110,
        // M undoable
        'n' | 'N' => 0b0001_0101,
        'o' | 'O' => 0b0111_1110,
        'p' | 'P' => 0b0110_0111,
        'q' => 0b0111_0011,
        // R undoable
        's' | 'S' => 0b0101_1011,
        // T undoable
        'u' | 'U' => 0b0011_1110,
        // V undoable
        // W undoable
        // X undoable
        // Y undoable
        // Z undoable
        _ => 0b1110_0101, // ?
    };

    if dot {
        result |= 0b1000_0000; // turn "." on
    }

    result
}

///
/// Convert the integer into an integer byte Sequence
///
fn base_10_bytes(mut n: i32, buf: &mut [u8]) -> &[u8] {
    let mut sign: bool = false;
    //don't overflow the display
    if !(-9999999..99999999).contains(&n) {
        return b"Err";
    }
    if n == 0 {
        return b"0";
    }
    if n < 0 {
        n = -n;
        sign = true;
    }
    let mut i = 0;
    while n > 0 {
        buf[i] = (n % 10) as u8 + b'0';
        n /= 10;
        i += 1;
    }
    if sign {
        buf[i] = b'-';
        i += 1;
    }
    let slice = &mut buf[..i];
    slice.reverse();
    &*slice
}

//
/// Convert the integer into a hexidecimal byte Sequence
///
fn hex_bytes(mut n: u32, buf: &mut [u8]) -> &[u8] {
    // don't overflow the display ( 0xFFFFFFF)
    if n == 0 {
        return b"0";
    }
    let mut i = 0;
    while n > 0 {
        let digit = (n % 16) as u8;
        buf[i] = match digit {
            0 => b'0',
            1 => b'1',
            2 => b'2',
            3 => b'3',
            4 => b'4',
            5 => b'5',
            6 => b'6',
            7 => b'7',
            8 => b'8',
            9 => b'9',
            10 => b'a',
            11 => b'b',
            12 => b'c',
            13 => b'd',
            14 => b'e',
            15 => b'f',
            _ => b'?',
        };
        n /= 16;
        i += 1;
    }
    let slice = &mut buf[..i];
    slice.reverse();
    &*slice
}

///
/// Take a byte slice and pad the left hand side
///
fn pad_left(val: &[u8]) -> [u8; 8] {
    assert!(val.len() <= 8);
    let size: usize = 8;
    let pos: usize = val.len();
    let mut cur: usize = 1;
    let mut out: [u8; 8] = *b"        ";
    while cur <= pos {
        out[size - cur] = val[pos - cur];
        cur += 1;
    }
    out
}
