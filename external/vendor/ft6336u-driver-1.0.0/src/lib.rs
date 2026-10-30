//! # FT6336U Capacitive Touch Controller Driver
//!
//! A platform-agnostic driver for the FT6336U capacitive touch controller using the
//! [`embedded-hal`](https://docs.rs/embedded-hal) I2C traits.
//!
//! ## Features
//!
//! - No `std` dependency - works in embedded environments
//! - Uses `embedded-hal` I2C traits for portability
//! - Support for up to 2 simultaneous touch points
//! - Gesture detection capabilities
//! - Configurable power modes and scan rates
//! - Comprehensive register access
//!
//! ## Quick Start
//!
//! ```rust,no_run
//! # use embedded_hal::i2c::I2c;
//! # use core::convert::Infallible;
//! # struct MockI2c;
//! # impl embedded_hal::i2c::ErrorType for MockI2c {
//! #     type Error = Infallible;
//! # }
//! # impl I2c for MockI2c {
//! #     fn write(&mut self, _: u8, _: &[u8]) -> Result<(), Self::Error> { Ok(()) }
//! #     fn read(&mut self, _: u8, _: &mut [u8]) -> Result<(), Self::Error> { Ok(()) }
//! #     fn write_read(&mut self, _: u8, _: &[u8], _: &mut [u8]) -> Result<(), Self::Error> { Ok(()) }
//! #     fn transaction(&mut self, _: u8, _: &mut [embedded_hal::i2c::Operation<'_>]) -> Result<(), Self::Error> { Ok(()) }
//! # }
//! # let i2c = MockI2c;
//! use ft6336u_driver::FT6336U;
//!
//! // Create the driver with your I2C peripheral
//! let mut touch = FT6336U::new(i2c);
//!
//! // Scan for touch events
//! let touch_data = touch.scan().unwrap();
//!
//! if touch_data.touch_count > 0 {
//!     let point = &touch_data.points[0];
//!     println!("Touch at ({}, {})", point.x, point.y);
//! }
//! ```
//!
//! ## Hardware Integration
//!
//! The FT6336U communicates over I2C at address `0x38`. It requires:
//! - An I2C bus connection (SDA/SCL)
//! - A reset pin (typically controlled by GPIO or GPIO expander)
//! - An interrupt pin (optional, for event-driven operation)
//!
//! ### Interrupt-Driven Operation
//!
//! For optimal power efficiency, configure the touch controller's interrupt pin
//! and use it to trigger touch scans only when needed:
//!
//! ```rust,no_run
//! # use embedded_hal::i2c::I2c;
//! # use core::convert::Infallible;
//! # struct MockI2c;
//! # impl embedded_hal::i2c::ErrorType for MockI2c {
//! #     type Error = Infallible;
//! # }
//! # impl I2c for MockI2c {
//! #     fn write(&mut self, _: u8, _: &[u8]) -> Result<(), Self::Error> { Ok(()) }
//! #     fn read(&mut self, _: u8, _: &mut [u8]) -> Result<(), Self::Error> { Ok(()) }
//! #     fn write_read(&mut self, _: u8, _: &[u8], _: &mut [u8]) -> Result<(), Self::Error> { Ok(()) }
//! #     fn transaction(&mut self, _: u8, _: &mut [embedded_hal::i2c::Operation<'_>]) -> Result<(), Self::Error> { Ok(()) }
//! # }
//! # let i2c = MockI2c;
//! use ft6336u_driver::{FT6336U, GestureMode};
//!
//! let mut touch = FT6336U::new(i2c);
//!
//! // Enable interrupt mode
//! touch.write_g_mode(GestureMode::Trigger).unwrap();
//!
//! // In your interrupt handler:
//! // let data = touch.scan().unwrap();
//! ```

#![no_std]
#![deny(missing_docs)]
#![deny(unsafe_code)]

mod ft6336u;

// Re-export the public API
pub use ft6336u::*;
