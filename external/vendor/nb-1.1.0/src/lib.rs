//! Minimal and reusable non-blocking I/O layer
//!
//! The ultimate goal of this crate is *code reuse*. With this crate you can
//! write *core* I/O APIs that can then be adapted to operate in either blocking
//! or non-blocking manner. Furthermore those APIs are not tied to a particular
//! asynchronous model and can be adapted to work with the `futures` model or
//! with the `async` / `await` model.
//!
//! # Core idea
//!
//! The [`WouldBlock`](enum.Error.html) error variant signals that the operation
//! can't be completed *right now* and would need to block to complete.
//! [`WouldBlock`](enum.Error.html) is a special error in the sense that's not
//! *fatal*; the operation can still be completed by retrying again later.
//!
//! [`nb::Result`](type.Result.html) is based on the API of
//! [`std::io::Result`](https://doc.rust-lang.org/std/io/type.Result.html),
//! which has a `WouldBlock` variant in its
//! [`ErrorKind`](https://doc.rust-lang.org/std/io/enum.ErrorKind.html).
//!
//! We can map [`WouldBlock`](enum.Error.html) to different blocking and
//! non-blocking models:
//!
//! - In blocking mode: [`WouldBlock`](enum.Error.html) means try again right
//!   now (i.e. busy wait)
//! - In `futures` mode: [`WouldBlock`](enum.Error.html) means
//!   [`Async::NotReady`](https://docs.rs/futures)
//! - In `await` mode: [`WouldBlock`](enum.Error.html) means `yield`
//!   (suspend the generator)
//!
//! # How to use this crate
//!
//! Application specific errors can be put inside the `Other` variant in the
//! [`nb::Error`](enum.Error.html) enum.
//!
//! So in your API instead of returning `Result<T, MyError>` return
//! `nb::Result<T, MyError>`
//!
//! ```
//! enum MyError {
//!     ThisError,
//!     ThatError,
//!     // ..
//! }
//!
//! // This is a blocking function, so it returns a normal `Result`
//! fn before() -> Result<(), MyError> {
//!     // ..
//! #   Ok(())
//! }
//!
//! // This is now a potentially (read: *non*) blocking function so it returns `nb::Result`
//! // instead of blocking
//! fn after() -> nb::Result<(), MyError> {
//!     // ..
//! #   Ok(())
//! }
//! ```
//!
//! You can use `Infallible` to signal that some API has no fatal
//! errors but may block:
//!
//! ```
//! use core::convert::Infallible;
//!
//! // This returns `Ok(())` or `Err(nb::Error::WouldBlock)`
//! fn maybe_blocking_api() -> nb::Result<(), Infallible> {
//!     // ..
//! #   Ok(())
//! }
//! ```
//!
//! Once your API uses [`nb::Result`] you can leverage the [`block!`], macro
//! to adapt it for blocking operation, or handle scheduling yourself.
//!
//! [`block!`]: macro.block.html
//! [`nb::Result`]: type.Result.html
//!
//! # Examples
//!
//! ## A Core I/O API
//!
//! Imagine the code (crate) below represents a Hardware Abstraction Layer for some microcontroller
//! (or microcontroller family).
//!
//! *In this and the following examples let's assume for simplicity that peripherals are treated
//! as global singletons and that no preemption is possible (i.e. interrupts are disabled).*
//!
//! ```
//! # use core::convert::Infallible;
//! // This is the `hal` crate
//! use nb;
//!
//! /// An LED
//! pub struct Led;
//!
//! impl Led {
//!     pub fn off(&self) {
//!         // ..
//!     }
//!     pub fn on(&self) {
//!         // ..
//!     }
//! }
//!
//! /// Serial interface
//! pub struct Serial;
//! pub enum Error {
//!     Overrun,
//!     // ..
//! }
//!
//! impl Serial {
//!     /// Reads a single byte from the serial interface
//!     pub fn read(&self) -> nb::Result<u8, Error> {
//!         // ..
//! #       Ok(0)
//!     }
//!
//!     /// Writes a single byte to the serial interface
//!     pub fn write(&self, byte: u8) -> nb::Result<(), Error> {
//!         // ..
//! #       Ok(())
//!     }
//! }
//!
//! /// A timer used for timeouts
//! pub struct Timer;
//!
//! impl Timer {
//!     /// Waits until the timer times out
//!     pub fn wait(&self) -> nb::Result<(), Infallible> {
//!         //^ NOTE the `Infallible` indicates that this operation can block but has no
//!         //  other form of error
//!
//!         // ..
//! #       Ok(())
//!     }
//! }
//! ```
//!
//! ## Blocking mode
//!
//! Turn on an LED for one second and *then* loops back serial data.
//!
//! ```
//! use core::convert::Infallible;
//! use nb::block;
//!
//! use hal::{Led, Serial, Timer};
//!
//! # fn main() -> Result<(), Infallible> {
//! // Turn the LED on for one second
//! Led.on();
//! block!(Timer.wait())?;
//! Led.off();
//!
//! // Serial interface loopback
//! # return Ok(());
//! loop {
//!     let byte = block!(Serial.read())?;
//!     block!(Serial.write(byte))?;
//! }
//! # }
//!
//! # mod hal {
//! #   use nb;
//! #   use core::convert::Infallible;
//! #   pub struct Led;
//! #   impl Led {
//! #       pub fn off(&self) {}
//! #       pub fn on(&self) {}
//! #   }
//! #   pub struct Serial;
//! #   impl Serial {
//! #       pub fn read(&self) -> nb::Result<u8, Infallible> { Ok(0) }
//! #       pub fn write(&self, _: u8) -> nb::Result<(), Infallible> { Ok(()) }
//! #   }
//! #   pub struct Timer;
//! #   impl Timer {
//! #       pub fn wait(&self) -> nb::Result<(), Infallible> { Ok(()) }
//! #   }
//! # }
//! ```
//!
//! # Features
//!
//! - `defmt-0-3` - unstable feature which adds [`defmt::Format`] impl for [`Error`].

#![no_std]

use core::fmt;

/// A non-blocking result
pub type Result<T, E> = ::core::result::Result<T, Error<E>>;

/// A non-blocking error
///
/// The main use of this enum is to add a `WouldBlock` variant to an existing
/// error enum.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Error<E> {
    /// A different kind of error
    Other(E),
    /// This operation requires blocking behavior to complete
    WouldBlock,
}

#[cfg(feature = "defmt-0-3")]
impl<E> defmt::Format for Error<E>
where
    E: defmt::Format,
{
    fn format(&self, f: defmt::Formatter) {
        match *self {
            Error::Other(ref e) => defmt::Format::format(e, f),
            Error::WouldBlock => defmt::write!(f, "WouldBlock",),
        }
    }
}

impl<E> fmt::Debug for Error<E>
where
    E: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::Other(ref e) => fmt::Debug::fmt(e, f),
            Error::WouldBlock => f.write_str("WouldBlock"),
        }
    }
}

impl<E> Error<E> {
    /// Maps an `Error<E>` to `Error<T>` by applying a function to a contained
    /// `Error::Other` value, leaving an `Error::WouldBlock` value untouched.
    pub fn map<T, F>(self, op: F) -> Error<T>
    where
        F: FnOnce(E) -> T,
    {
        match self {
            Error::Other(e) => Error::Other(op(e)),
            Error::WouldBlock => Error::WouldBlock,
        }
    }
}

impl<E> From<E> for Error<E> {
    fn from(error: E) -> Error<E> {
        Error::Other(error)
    }
}

/// Turns the non-blocking expression `$e` into a blocking operation.
///
/// This is accomplished by continuously calling the expression `$e` until it no
/// longer returns `Error::WouldBlock`
///
/// # Input
///
/// An expression `$e` that evaluates to `nb::Result<T, E>`
///
/// # Output
///
/// - `Ok(t)` if `$e` evaluates to `Ok(t)`
/// - `Err(e)` if `$e` evaluates to `Err(nb::Error::Other(e))`
#[macro_export]
macro_rules! block {
    ($e:expr) => {
        loop {
            #[allow(unreachable_patterns)]
            match $e {
                Err($crate::Error::Other(e)) =>
                {
                    #[allow(unreachable_code)]
                    break Err(e)
                }
                Err($crate::Error::WouldBlock) => {}
                Ok(x) => break Ok(x),
            }
        }
    };
}
