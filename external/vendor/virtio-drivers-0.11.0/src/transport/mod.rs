//! VirtIO transports.

#[cfg(test)]
pub mod fake;
pub mod mmio;
pub mod pci;
mod some;
#[cfg(target_arch = "x86_64")]
pub mod x86_64;

use crate::{PhysAddr, Result, PAGE_SIZE};
use bitflags::{bitflags, Flags};
use core::{
    fmt::{self, Debug, Formatter},
    ops::BitAnd,
};
use log::debug;
pub use some::SomeTransport;
use thiserror::Error;
use zerocopy::{FromBytes, Immutable, IntoBytes};

/// A VirtIO transport layer.
pub trait Transport {
    /// Gets the device type.
    fn device_type(&self) -> DeviceType;

    /// Reads device features.
    fn read_device_features(&mut self) -> u64;

    /// Writes device features.
    fn write_driver_features(&mut self, driver_features: u64);

    /// Gets the max size of the given queue.
    fn max_queue_size(&mut self, queue: u16) -> u32;

    /// Notifies the given queue on the device.
    fn notify(&mut self, queue: u16);

    /// Gets the device status.
    fn get_status(&self) -> DeviceStatus;

    /// Sets the device status.
    fn set_status(&mut self, status: DeviceStatus);

    /// Sets the guest page size.
    fn set_guest_page_size(&mut self, guest_page_size: u32);

    /// Returns whether the transport requires queues to use the legacy layout.
    ///
    /// Ref: 2.6.2 Legacy Interfaces: A Note on Virtqueue Layout
    fn requires_legacy_layout(&self) -> bool;

    /// Sets up the given queue.
    fn queue_set(
        &mut self,
        queue: u16,
        size: u32,
        descriptors: PhysAddr,
        driver_area: PhysAddr,
        device_area: PhysAddr,
    );

    /// Disables and resets the given queue.
    fn queue_unset(&mut self, queue: u16);

    /// Returns whether the queue is in use, i.e. has a nonzero PFN or is marked as ready.
    fn queue_used(&mut self, queue: u16) -> bool;

    /// Acknowledges an interrupt.
    ///
    /// Returns true on success.
    fn ack_interrupt(&mut self) -> bool;

    /// Begins initializing the device.
    ///
    /// Ref: virtio 3.1.1 Device Initialization
    ///
    /// Returns the negotiated set of features.
    fn begin_init<F: Flags<Bits = u64> + BitAnd<Output = F> + Debug>(
        &mut self,
        supported_features: F,
    ) -> F {
        self.set_status(DeviceStatus::empty());
        self.set_status(DeviceStatus::ACKNOWLEDGE | DeviceStatus::DRIVER);

        let device_features = F::from_bits_truncate(self.read_device_features());
        debug!("Device features: {:?}", device_features);
        let negotiated_features = device_features & supported_features;
        self.write_driver_features(negotiated_features.bits());

        self.set_status(
            DeviceStatus::ACKNOWLEDGE | DeviceStatus::DRIVER | DeviceStatus::FEATURES_OK,
        );

        self.set_guest_page_size(PAGE_SIZE as u32);

        negotiated_features
    }

    /// Finishes initializing the device.
    fn finish_init(&mut self) {
        self.set_status(
            DeviceStatus::ACKNOWLEDGE
                | DeviceStatus::DRIVER
                | DeviceStatus::FEATURES_OK
                | DeviceStatus::DRIVER_OK,
        );
    }

    /// Reads the configuration space generation.
    fn read_config_generation(&self) -> u32;

    /// Reads a value from the device config space.
    fn read_config_space<T: FromBytes + IntoBytes>(&self, offset: usize) -> Result<T>;

    /// Writes a value to the device config space.
    fn write_config_space<T: IntoBytes + Immutable>(
        &mut self,
        offset: usize,
        value: T,
    ) -> Result<()>;

    /// Safely reads multiple fields from config space by ensuring that the config generation is the
    /// same before and after all reads, and retrying if not.
    fn read_consistent<T>(&self, f: impl Fn() -> Result<T>) -> Result<T> {
        loop {
            let before = self.read_config_generation();
            let result = f();
            let after = self.read_config_generation();
            if before == after {
                break result;
            }
        }
    }
}

/// The device status field. Writing 0 into this field resets the device.
#[derive(Copy, Clone, Default, Eq, FromBytes, Immutable, IntoBytes, PartialEq)]
pub struct DeviceStatus(u32);

impl Debug for DeviceStatus {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "DeviceStatus(")?;
        bitflags::parser::to_writer(self, &mut *f)?;
        write!(f, ")")?;
        Ok(())
    }
}

bitflags! {
    impl DeviceStatus: u32 {
        /// Indicates that the guest OS has found the device and recognized it
        /// as a valid virtio device.
        const ACKNOWLEDGE = 1;

        /// Indicates that the guest OS knows how to drive the device.
        const DRIVER = 2;

        /// Indicates that something went wrong in the guest, and it has given
        /// up on the device. This could be an internal error, or the driver
        /// didn’t like the device for some reason, or even a fatal error
        /// during device operation.
        const FAILED = 128;

        /// Indicates that the driver has acknowledged all the features it
        /// understands, and feature negotiation is complete.
        const FEATURES_OK = 8;

        /// Indicates that the driver is set up and ready to drive the device.
        const DRIVER_OK = 4;

        /// Indicates that the device has experienced an error from which it
        /// can’t recover.
        const DEVICE_NEEDS_RESET = 64;
    }
}

/// Types of virtio devices.
#[repr(u8)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(missing_docs)]
pub enum DeviceType {
    Network = 1,
    Block = 2,
    Console = 3,
    EntropySource = 4,
    MemoryBallooning = 5,
    IoMemory = 6,
    Rpmsg = 7,
    ScsiHost = 8,
    _9P = 9,
    Mac80211 = 10,
    RprocSerial = 11,
    VirtioCAIF = 12,
    MemoryBalloon = 13,
    GPU = 16,
    Timer = 17,
    Input = 18,
    Socket = 19,
    Crypto = 20,
    SignalDistributionModule = 21,
    Pstore = 22,
    IOMMU = 23,
    Memory = 24,
    Sound = 25,
}

/// Errors converting a number to a virtio device type.
#[derive(Copy, Clone, Debug, Eq, Error, PartialEq)]
pub enum DeviceTypeError {
    /// Invalid or unknown virtio device type.
    #[error("Invalid or unknown virtio device type {0}")]
    InvalidDeviceType(u32),
}

impl TryFrom<u32> for DeviceType {
    type Error = DeviceTypeError;

    fn try_from(virtio_device_id: u32) -> core::result::Result<Self, Self::Error> {
        match virtio_device_id {
            1 => Ok(DeviceType::Network),
            2 => Ok(DeviceType::Block),
            3 => Ok(DeviceType::Console),
            4 => Ok(DeviceType::EntropySource),
            5 => Ok(DeviceType::MemoryBalloon),
            6 => Ok(DeviceType::IoMemory),
            7 => Ok(DeviceType::Rpmsg),
            8 => Ok(DeviceType::ScsiHost),
            9 => Ok(DeviceType::_9P),
            10 => Ok(DeviceType::Mac80211),
            11 => Ok(DeviceType::RprocSerial),
            12 => Ok(DeviceType::VirtioCAIF),
            13 => Ok(DeviceType::MemoryBalloon),
            16 => Ok(DeviceType::GPU),
            17 => Ok(DeviceType::Timer),
            18 => Ok(DeviceType::Input),
            19 => Ok(DeviceType::Socket),
            20 => Ok(DeviceType::Crypto),
            21 => Ok(DeviceType::SignalDistributionModule),
            22 => Ok(DeviceType::Pstore),
            23 => Ok(DeviceType::IOMMU),
            24 => Ok(DeviceType::Memory),
            25 => Ok(DeviceType::Sound),
            _ => Err(DeviceTypeError::InvalidDeviceType(virtio_device_id)),
        }
    }
}

impl TryFrom<u16> for DeviceType {
    type Error = DeviceTypeError;

    fn try_from(virtio_device_id: u16) -> core::result::Result<Self, Self::Error> {
        u32::from(virtio_device_id).try_into()
    }
}

impl TryFrom<u8> for DeviceType {
    type Error = DeviceTypeError;

    fn try_from(virtio_device_id: u8) -> core::result::Result<Self, Self::Error> {
        u32::from(virtio_device_id).try_into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn debug_device_status() {
        let status = DeviceStatus::from_bits_retain(0x23);
        assert_eq!(
            format!("{:?}", status),
            "DeviceStatus(ACKNOWLEDGE | DRIVER | 0x20)"
        );
    }
}
