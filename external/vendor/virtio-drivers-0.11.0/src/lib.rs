//! VirtIO guest drivers.
//!
//! These drivers can be used by bare-metal code (such as a bootloader or OS kernel) running in a VM
//! to interact with VirtIO devices provided by the VMM (such as QEMU or crosvm).
//!
//! # Usage
//!
//! You must first implement the [`Hal`] trait, to allocate DMA regions and translate between
//! physical addresses (as seen by devices) and virtual addresses (as seen by your program). You can
//! then construct the appropriate transport for the VirtIO device, e.g. for an MMIO device (perhaps
//! discovered from the device tree):
//!
//! ```
//! use core::ptr::NonNull;
//! use virtio_drivers::transport::mmio::{MmioTransport, VirtIOHeader};
//!
//! # fn example(mmio_device_address: usize, mmio_size: usize) {
//! let header = NonNull::new(mmio_device_address as *mut VirtIOHeader).unwrap();
//! let transport = unsafe { MmioTransport::new(header, mmio_size) }.unwrap();
//! # }
//! ```
//!
//! You can then check what kind of VirtIO device it is and construct the appropriate driver:
//!
//! ```
//! # use virtio_drivers::Hal;
//! # #[cfg(feature = "alloc")]
//! use virtio_drivers::{
//!     device::console::VirtIOConsole,
//!     transport::{mmio::MmioTransport, DeviceType, Transport},
//! };

//!
//! # #[cfg(feature = "alloc")]
//! # fn example<HalImpl: Hal>(transport: MmioTransport) {
//! if transport.device_type() == DeviceType::Console {
//!     let mut console = VirtIOConsole::<HalImpl, _>::new(transport).unwrap();
//!     // Send a byte to the console.
//!     console.send(b'H').unwrap();
//! }
//! # }
//! ```

#![cfg_attr(not(test), no_std)]
#![deny(unused_must_use, missing_docs, clippy::undocumented_unsafe_blocks)]
#![allow(clippy::identity_op)]
#![allow(dead_code)]

#[cfg(any(feature = "alloc", test))]
extern crate alloc;

mod config;
pub mod device;
#[cfg(feature = "embedded-io")]
mod embedded_io;
mod hal;
mod queue;
pub mod transport;

use device::socket::SocketError;
use thiserror::Error;

pub use self::hal::{BufferDirection, Hal, PhysAddr};
pub use safe_mmio::UniqueMmioPointer;

/// The page size in bytes supported by the library (4 KiB).
pub const PAGE_SIZE: usize = 0x1000;

/// The type returned by driver methods.
pub type Result<T = ()> = core::result::Result<T, Error>;

/// The error type of VirtIO drivers.
#[derive(Copy, Clone, Debug, Eq, Error, PartialEq)]
pub enum Error {
    /// There are not enough descriptors available in the virtqueue, try again later.
    #[error("Virtqueue is full")]
    QueueFull,
    /// The device is not ready.
    #[error("Device not ready")]
    NotReady,
    /// The device used a different descriptor chain to the one we were expecting.
    #[error("Device used a different descriptor chain to the one we were expecting")]
    WrongToken,
    /// The queue is already in use.
    #[error("Virtqueue is already in use")]
    AlreadyUsed,
    /// Invalid parameter.
    #[error("Invalid parameter")]
    InvalidParam,
    /// Failed to allocate DMA memory.
    #[error("Failed to allocate DMA memory")]
    DmaError,
    /// I/O error
    #[error("I/O error")]
    IoError,
    /// The request was not supported by the device.
    #[error("Request not supported by device")]
    Unsupported,
    /// The config space advertised by the device is smaller than the driver expected.
    #[error("Config space advertised by the device is smaller than expected")]
    ConfigSpaceTooSmall,
    /// The device doesn't have any config space, but the driver expects some.
    #[error("The device doesn't have any config space, but the driver expects some")]
    ConfigSpaceMissing,
    /// Error from the socket device.
    #[error("Error from the socket device: {0}")]
    SocketDeviceError(#[from] SocketError),
}

#[cfg(feature = "alloc")]
impl From<alloc::string::FromUtf8Error> for Error {
    fn from(_value: alloc::string::FromUtf8Error) -> Self {
        Self::IoError
    }
}

/// Align `size` up to a page.
fn align_up(size: usize) -> usize {
    (size + PAGE_SIZE) & !(PAGE_SIZE - 1)
}

/// The number of pages required to store `size` bytes, rounded up to a whole number of pages.
fn pages(size: usize) -> usize {
    size.div_ceil(PAGE_SIZE)
}
