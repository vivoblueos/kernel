//! Error types for the FT6336U driver.
//!
//! This module defines the error types that can occur during
//! communication with the touch controller.

/// Errors that can occur during FT6336U operations
///
/// # Examples
///
/// ```rust
/// use ft6336u_driver::Error;
///
/// // The error type is generic over the I2C error type
/// let err: Error<()> = Error::InvalidData;
/// ```
#[derive(Debug)]
pub enum Error<E> {
    /// I2C communication error
    I2c(E),
    /// Invalid data received from device
    InvalidData,
}

impl<E> From<E> for Error<E> {
    fn from(e: E) -> Self {
        Self::I2c(e)
    }
}
