//! PCI transport for VirtIO.

pub mod bus;

use self::bus::{
    ConfigurationAccess, DeviceFunction, DeviceFunctionInfo, PciError, PciRoot, PCI_CAP_ID_VNDR,
};
use super::{DeviceStatus, DeviceType, Transport};
use crate::{
    hal::{Hal, PhysAddr},
    Error,
};
use core::{
    mem::{align_of, size_of},
    ops::Deref,
    ptr::NonNull,
};
use safe_mmio::{
    field, field_shared,
    fields::{ReadOnly, ReadPure, ReadPureWrite, WriteOnly},
    UniqueMmioPointer,
};
use zerocopy::{FromBytes, Immutable, IntoBytes};

/// The PCI vendor ID for VirtIO devices.
pub const VIRTIO_VENDOR_ID: u16 = 0x1af4;

/// The offset to add to a VirtIO device ID to get the corresponding PCI device ID.
const PCI_DEVICE_ID_OFFSET: u16 = 0x1040;

const TRANSITIONAL_NETWORK: u16 = 0x1000;
const TRANSITIONAL_BLOCK: u16 = 0x1001;
const TRANSITIONAL_MEMORY_BALLOONING: u16 = 0x1002;
const TRANSITIONAL_CONSOLE: u16 = 0x1003;
const TRANSITIONAL_SCSI_HOST: u16 = 0x1004;
const TRANSITIONAL_ENTROPY_SOURCE: u16 = 0x1005;
const TRANSITIONAL_9P_TRANSPORT: u16 = 0x1009;

/// The offset of the bar field within `virtio_pci_cap`.
pub(crate) const CAP_BAR_OFFSET: u8 = 4;
/// The offset of the offset field with `virtio_pci_cap`.
pub(crate) const CAP_BAR_OFFSET_OFFSET: u8 = 8;
/// The offset of the `length` field within `virtio_pci_cap`.
pub(crate) const CAP_LENGTH_OFFSET: u8 = 12;
/// The offset of the`notify_off_multiplier` field within `virtio_pci_notify_cap`.
pub(crate) const CAP_NOTIFY_OFF_MULTIPLIER_OFFSET: u8 = 16;

/// Common configuration.
pub const VIRTIO_PCI_CAP_COMMON_CFG: u8 = 1;
/// Notifications.
pub const VIRTIO_PCI_CAP_NOTIFY_CFG: u8 = 2;
/// ISR Status.
pub const VIRTIO_PCI_CAP_ISR_CFG: u8 = 3;
/// Device specific configuration.
pub const VIRTIO_PCI_CAP_DEVICE_CFG: u8 = 4;

pub(crate) fn device_type(pci_device_id: u16) -> Option<DeviceType> {
    match pci_device_id {
        TRANSITIONAL_NETWORK => Some(DeviceType::Network),
        TRANSITIONAL_BLOCK => Some(DeviceType::Block),
        TRANSITIONAL_MEMORY_BALLOONING => Some(DeviceType::MemoryBalloon),
        TRANSITIONAL_CONSOLE => Some(DeviceType::Console),
        TRANSITIONAL_SCSI_HOST => Some(DeviceType::ScsiHost),
        TRANSITIONAL_ENTROPY_SOURCE => Some(DeviceType::EntropySource),
        TRANSITIONAL_9P_TRANSPORT => Some(DeviceType::_9P),
        id if id >= PCI_DEVICE_ID_OFFSET => DeviceType::try_from(id - PCI_DEVICE_ID_OFFSET).ok(),
        _ => None,
    }
}

/// Returns the type of VirtIO device to which the given PCI vendor and device ID corresponds, or
/// `None` if it is not a recognised VirtIO device.
pub fn virtio_device_type(device_function_info: &DeviceFunctionInfo) -> Option<DeviceType> {
    if device_function_info.vendor_id == VIRTIO_VENDOR_ID {
        device_type(device_function_info.device_id)
    } else {
        None
    }
}

/// PCI transport for VirtIO.
///
/// Ref: 4.1 Virtio Over PCI Bus
#[derive(Debug)]
pub struct PciTransport {
    device_type: DeviceType,
    /// The bus, device and function identifier for the VirtIO device.
    device_function: DeviceFunction,
    /// The common configuration structure within some BAR.
    common_cfg: UniqueMmioPointer<'static, CommonCfg>,
    /// The start of the queue notification region within some BAR.
    notify_region: UniqueMmioPointer<'static, [WriteOnly<u16>]>,
    notify_off_multiplier: u32,
    /// The ISR status register within some BAR.
    isr_status: UniqueMmioPointer<'static, ReadOnly<u8>>,
    /// The VirtIO device-specific configuration within some BAR.
    config_space: Option<UniqueMmioPointer<'static, [u32]>>,
}

impl PciTransport {
    /// Construct a new PCI VirtIO device driver for the given device function on the given PCI
    /// root controller.
    ///
    /// The PCI device must already have had its BARs allocated.
    pub fn new<H: Hal, C: ConfigurationAccess>(
        root: &mut PciRoot<C>,
        device_function: DeviceFunction,
    ) -> Result<Self, VirtioPciError> {
        let device_vendor = root.configuration_access.read_word(device_function, 0);
        let device_id = (device_vendor >> 16) as u16;
        let vendor_id = device_vendor as u16;
        if vendor_id != VIRTIO_VENDOR_ID {
            return Err(VirtioPciError::InvalidVendorId(vendor_id));
        }
        let device_type =
            device_type(device_id).ok_or(VirtioPciError::InvalidDeviceId(device_id))?;

        // Find the PCI capabilities we need.
        let mut common_cfg = None;
        let mut notify_cfg = None;
        let mut notify_off_multiplier = 0;
        let mut isr_cfg = None;
        let mut device_cfg = None;
        for capability in root.capabilities(device_function) {
            if capability.id != PCI_CAP_ID_VNDR {
                continue;
            }
            let cap_len = capability.private_header as u8;
            let cfg_type = (capability.private_header >> 8) as u8;
            if cap_len < 16 {
                continue;
            }
            let struct_info = VirtioCapabilityInfo {
                bar: root
                    .configuration_access
                    .read_word(device_function, capability.offset + CAP_BAR_OFFSET)
                    as u8,
                offset: root
                    .configuration_access
                    .read_word(device_function, capability.offset + CAP_BAR_OFFSET_OFFSET),
                length: root
                    .configuration_access
                    .read_word(device_function, capability.offset + CAP_LENGTH_OFFSET),
            };

            match cfg_type {
                VIRTIO_PCI_CAP_COMMON_CFG if common_cfg.is_none() => {
                    common_cfg = Some(struct_info);
                }
                VIRTIO_PCI_CAP_NOTIFY_CFG if cap_len >= 20 && notify_cfg.is_none() => {
                    notify_cfg = Some(struct_info);
                    notify_off_multiplier = root.configuration_access.read_word(
                        device_function,
                        capability.offset + CAP_NOTIFY_OFF_MULTIPLIER_OFFSET,
                    );
                }
                VIRTIO_PCI_CAP_ISR_CFG if isr_cfg.is_none() => {
                    isr_cfg = Some(struct_info);
                }
                VIRTIO_PCI_CAP_DEVICE_CFG if device_cfg.is_none() => {
                    device_cfg = Some(struct_info);
                }
                _ => {}
            }
        }

        let common_cfg = get_bar_region::<H, _, _>(
            root,
            device_function,
            &common_cfg.ok_or(VirtioPciError::MissingCommonConfig)?,
        )?;
        // SAFETY: `get_bar_region` should always return a valid MMIO region, assuming the PCI root
        // is behaving.
        let common_cfg = unsafe { UniqueMmioPointer::new(common_cfg) };

        let notify_cfg = notify_cfg.ok_or(VirtioPciError::MissingNotifyConfig)?;
        if notify_off_multiplier % 2 != 0 {
            return Err(VirtioPciError::InvalidNotifyOffMultiplier(
                notify_off_multiplier,
            ));
        }
        let notify_region = get_bar_region_slice::<H, _, _>(root, device_function, &notify_cfg)?;
        // SAFETY: `get_bar_region` should always return a valid MMIO region, assuming the PCI root
        // is behaving.
        let notify_region = unsafe { UniqueMmioPointer::new(notify_region) };

        let isr_status = get_bar_region::<H, _, _>(
            root,
            device_function,
            &isr_cfg.ok_or(VirtioPciError::MissingIsrConfig)?,
        )?;
        // SAFETY: `get_bar_region` should always return a valid MMIO region, assuming the PCI root
        // is behaving.
        let isr_status = unsafe { UniqueMmioPointer::new(isr_status) };

        let config_space = if let Some(device_cfg) = device_cfg {
            // SAFETY: `get_bar_region_slice` should always return a valid MMIO region, assuming the
            // PCI root is behaving.
            Some(unsafe {
                UniqueMmioPointer::new(get_bar_region_slice::<H, _, _>(
                    root,
                    device_function,
                    &device_cfg,
                )?)
            })
        } else {
            None
        };

        Ok(Self {
            device_type,
            device_function,
            common_cfg,
            notify_region,
            notify_off_multiplier,
            isr_status,
            config_space,
        })
    }
}

impl Transport for PciTransport {
    fn device_type(&self) -> DeviceType {
        self.device_type
    }

    fn read_device_features(&mut self) -> u64 {
        field!(self.common_cfg, device_feature_select).write(0);
        let mut device_features_bits = field_shared!(self.common_cfg, device_feature).read() as u64;
        field!(self.common_cfg, device_feature_select).write(1);
        device_features_bits |=
            (field_shared!(self.common_cfg, device_feature).read() as u64) << 32;
        device_features_bits
    }

    fn write_driver_features(&mut self, driver_features: u64) {
        field!(self.common_cfg, driver_feature_select).write(0);
        field!(self.common_cfg, driver_feature).write(driver_features as u32);
        field!(self.common_cfg, driver_feature_select).write(1);
        field!(self.common_cfg, driver_feature).write((driver_features >> 32) as u32);
    }

    fn max_queue_size(&mut self, queue: u16) -> u32 {
        field!(self.common_cfg, queue_select).write(queue);
        field_shared!(self.common_cfg, queue_size).read().into()
    }

    fn notify(&mut self, queue: u16) {
        field!(self.common_cfg, queue_select).write(queue);
        // TODO: Consider caching this somewhere (per queue).
        let queue_notify_off = field_shared!(self.common_cfg, queue_notify_off).read();

        let offset_bytes = usize::from(queue_notify_off) * self.notify_off_multiplier as usize;
        let index = offset_bytes / size_of::<u16>();
        self.notify_region.get(index).unwrap().write(queue);
    }

    fn get_status(&self) -> DeviceStatus {
        let status = field_shared!(self.common_cfg, device_status).read();
        DeviceStatus::from_bits_truncate(status.into())
    }

    fn set_status(&mut self, status: DeviceStatus) {
        field!(self.common_cfg, device_status).write(status.bits() as u8);
    }

    fn set_guest_page_size(&mut self, _guest_page_size: u32) {
        // No-op, the PCI transport doesn't care.
    }

    fn requires_legacy_layout(&self) -> bool {
        false
    }

    fn queue_set(
        &mut self,
        queue: u16,
        size: u32,
        descriptors: PhysAddr,
        driver_area: PhysAddr,
        device_area: PhysAddr,
    ) {
        field!(self.common_cfg, queue_select).write(queue);
        field!(self.common_cfg, queue_size).write(size as u16);
        field!(self.common_cfg, queue_desc).write(descriptors as u64);
        field!(self.common_cfg, queue_driver).write(driver_area as u64);
        field!(self.common_cfg, queue_device).write(device_area as u64);
        field!(self.common_cfg, queue_enable).write(1);
    }

    fn queue_unset(&mut self, _queue: u16) {
        // The VirtIO spec doesn't allow queues to be unset once they have been set up for the PCI
        // transport, so this is a no-op.
    }

    fn queue_used(&mut self, queue: u16) -> bool {
        field!(self.common_cfg, queue_select).write(queue);
        field_shared!(self.common_cfg, queue_enable).read() == 1
    }

    fn ack_interrupt(&mut self) -> bool {
        // Reading the ISR status resets it to 0 and causes the device to de-assert the interrupt.
        let isr_status = self.isr_status.read();
        // TODO: Distinguish between queue interrupt and device configuration interrupt.
        isr_status & 0x3 != 0
    }

    fn read_config_generation(&self) -> u32 {
        field_shared!(self.common_cfg, config_generation)
            .read()
            .into()
    }

    fn read_config_space<T: FromBytes + IntoBytes>(&self, offset: usize) -> Result<T, Error> {
        assert!(align_of::<T>() <= 4,
            "Driver expected config space alignment of {} bytes, but VirtIO only guarantees 4 byte alignment.",
            align_of::<T>());
        assert_eq!(offset % align_of::<T>(), 0);

        let config_space = self
            .config_space
            .as_ref()
            .ok_or(Error::ConfigSpaceMissing)?;
        if config_space.len() * size_of::<u32>() < offset + size_of::<T>() {
            Err(Error::ConfigSpaceTooSmall)
        } else {
            // SAFETY: If we have a config space pointer it must be valid for its length, and we
            // just checked that the offset and size of the access was within the length and
            // properly aligned. Reading the config space shouldn't have side-effects.
            unsafe {
                let ptr = config_space.ptr().cast::<T>().byte_add(offset);
                Ok(config_space
                    .deref()
                    .child(NonNull::new(ptr.cast_mut()).unwrap())
                    .read_unsafe())
            }
        }
    }

    fn write_config_space<T: IntoBytes + Immutable>(
        &mut self,
        offset: usize,
        value: T,
    ) -> Result<(), Error> {
        assert!(align_of::<T>() <= 4,
            "Driver expected config space alignment of {} bytes, but VirtIO only guarantees 4 byte alignment.",
            align_of::<T>());
        assert_eq!(offset % align_of::<T>(), 0);

        let config_space = self
            .config_space
            .as_mut()
            .ok_or(Error::ConfigSpaceMissing)?;
        if config_space.len() * size_of::<u32>() < offset + size_of::<T>() {
            Err(Error::ConfigSpaceTooSmall)
        } else {
            // SAFETY: If we have a config space pointer it must be valid for its length, and we
            // just checked that the offset and size of the access was within the length and
            // properly aligned.
            unsafe {
                let ptr = config_space.ptr_nonnull().cast::<T>().byte_add(offset);
                config_space.child(ptr).write_unsafe(value);
            }
            Ok(())
        }
    }
}

// SAFETY: MMIO can be done from any thread or CPU core.
unsafe impl Send for PciTransport {}

// SAFETY: `&PciTransport` only allows MMIO reads or getting the config space, both of which are
// fine to happen concurrently on different CPU cores.
unsafe impl Sync for PciTransport {}

impl Drop for PciTransport {
    fn drop(&mut self) {
        // Reset the device when the transport is dropped.
        self.set_status(DeviceStatus::empty());
        while self.get_status() != DeviceStatus::empty() {}
    }
}

/// `virtio_pci_common_cfg`, see 4.1.4.3 "Common configuration structure layout".
#[repr(C)]
pub(crate) struct CommonCfg {
    pub device_feature_select: ReadPureWrite<u32>,
    pub device_feature: ReadPure<u32>,
    pub driver_feature_select: ReadPureWrite<u32>,
    pub driver_feature: ReadPureWrite<u32>,
    pub msix_config: ReadPureWrite<u16>,
    pub num_queues: ReadPure<u16>,
    pub device_status: ReadPureWrite<u8>,
    pub config_generation: ReadPure<u8>,
    pub queue_select: ReadPureWrite<u16>,
    pub queue_size: ReadPureWrite<u16>,
    pub queue_msix_vector: ReadPureWrite<u16>,
    pub queue_enable: ReadPureWrite<u16>,
    pub queue_notify_off: ReadPureWrite<u16>,
    pub queue_desc: ReadPureWrite<u64>,
    pub queue_driver: ReadPureWrite<u64>,
    pub queue_device: ReadPureWrite<u64>,
}

/// Information about a VirtIO structure within some BAR, as provided by a `virtio_pci_cap`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct VirtioCapabilityInfo {
    /// The bar in which the structure can be found.
    pub bar: u8,
    /// The offset within the bar.
    pub offset: u32,
    /// The length in bytes of the structure within the bar.
    pub length: u32,
}

fn get_bar_region<H: Hal, T, C: ConfigurationAccess>(
    root: &mut PciRoot<C>,
    device_function: DeviceFunction,
    struct_info: &VirtioCapabilityInfo,
) -> Result<NonNull<T>, VirtioPciError> {
    let bar_info = root
        .bar_info(device_function, struct_info.bar)?
        .ok_or(VirtioPciError::BarNotAllocated(struct_info.bar))?;
    let (bar_address, bar_size) = bar_info
        .memory_address_size()
        .ok_or(VirtioPciError::UnexpectedIoBar)?;
    if bar_address == 0 {
        return Err(VirtioPciError::BarNotAllocated(struct_info.bar));
    }
    if u64::from(struct_info.offset + struct_info.length) > bar_size
        || size_of::<T>() > struct_info.length as usize
    {
        return Err(VirtioPciError::BarOffsetOutOfRange);
    }
    let paddr = bar_address as PhysAddr + struct_info.offset as PhysAddr;
    // SAFETY: The paddr and size describe a valid MMIO region, at least according to the PCI bus.
    let vaddr = unsafe { H::mmio_phys_to_virt(paddr, struct_info.length as usize) };
    if vaddr.as_ptr() as usize % align_of::<T>() != 0 {
        return Err(VirtioPciError::Misaligned {
            address: vaddr.as_ptr() as usize,
            alignment: align_of::<T>(),
        });
    }
    Ok(vaddr.cast())
}

fn get_bar_region_slice<H: Hal, T, C: ConfigurationAccess>(
    root: &mut PciRoot<C>,
    device_function: DeviceFunction,
    struct_info: &VirtioCapabilityInfo,
) -> Result<NonNull<[T]>, VirtioPciError> {
    let ptr = get_bar_region::<H, T, C>(root, device_function, struct_info)?;
    Ok(NonNull::slice_from_raw_parts(
        ptr,
        struct_info.length as usize / size_of::<T>(),
    ))
}

/// An error encountered initialising a VirtIO PCI transport.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum VirtioPciError {
    /// PCI device ID was not a valid VirtIO device ID.
    #[error("PCI device ID {0:#06x} was not a valid VirtIO device ID.")]
    InvalidDeviceId(u16),
    /// PCI device vender ID was not the VirtIO vendor ID.
    #[error("PCI device vender ID {0:#06x} was not the VirtIO vendor ID {VIRTIO_VENDOR_ID:#06x}.")]
    InvalidVendorId(u16),
    /// No valid `VIRTIO_PCI_CAP_COMMON_CFG` capability was found.
    #[error("No valid `VIRTIO_PCI_CAP_COMMON_CFG` capability was found.")]
    MissingCommonConfig,
    /// No valid `VIRTIO_PCI_CAP_NOTIFY_CFG` capability was found.
    #[error("No valid `VIRTIO_PCI_CAP_NOTIFY_CFG` capability was found.")]
    MissingNotifyConfig,
    /// `VIRTIO_PCI_CAP_NOTIFY_CFG` capability has a `notify_off_multiplier` that is not a multiple
    /// of 2.
    #[error("`VIRTIO_PCI_CAP_NOTIFY_CFG` capability has a `notify_off_multiplier` that is not a multiple of 2: {0}")]
    InvalidNotifyOffMultiplier(u32),
    /// No valid `VIRTIO_PCI_CAP_ISR_CFG` capability was found.
    #[error("No valid `VIRTIO_PCI_CAP_ISR_CFG` capability was found.")]
    MissingIsrConfig,
    /// An IO BAR was provided rather than a memory BAR.
    #[error("Unexpected IO BAR (expected memory BAR).")]
    UnexpectedIoBar,
    /// A BAR which we need was not allocated an address.
    #[error("Bar {0} not allocated.")]
    BarNotAllocated(u8),
    /// The offset for some capability was greater than the length of the BAR.
    #[error("Capability offset greater than BAR length.")]
    BarOffsetOutOfRange,
    /// The address was not aligned as expected.
    #[error("Address {address:#018} was not aligned to a {alignment} byte boundary as expected.")]
    Misaligned {
        /// The address in question.
        address: usize,
        /// The expected alignment in bytes.
        alignment: usize,
    },
    /// A generic PCI error,
    #[error(transparent)]
    Pci(PciError),
}

impl From<PciError> for VirtioPciError {
    fn from(error: PciError) -> Self {
        Self::Pci(error)
    }
}

// SAFETY: The `vaddr` field of `VirtioPciError::Misaligned` is only used for debug output.
unsafe impl Send for VirtioPciError {}

// SAFETY: The `vaddr` field of `VirtioPciError::Misaligned` is only used for debug output.
unsafe impl Sync for VirtioPciError {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn transitional_device_ids() {
        assert_eq!(device_type(0x1000), Some(DeviceType::Network));
        assert_eq!(device_type(0x1002), Some(DeviceType::MemoryBalloon));
        assert_eq!(device_type(0x1009), Some(DeviceType::_9P));
    }

    #[test]
    fn offset_device_ids() {
        assert_eq!(device_type(0x1040), None);
        assert_eq!(device_type(0x1045), Some(DeviceType::MemoryBalloon));
        assert_eq!(device_type(0x1049), Some(DeviceType::_9P));
        assert_eq!(device_type(0x1058), Some(DeviceType::Memory));
        assert_eq!(device_type(0x1059), Some(DeviceType::Sound));
        assert_eq!(device_type(0x1060), None);
    }

    #[test]
    fn virtio_device_type_valid() {
        assert_eq!(
            virtio_device_type(&DeviceFunctionInfo {
                vendor_id: VIRTIO_VENDOR_ID,
                device_id: TRANSITIONAL_BLOCK,
                class: 0,
                subclass: 0,
                prog_if: 0,
                revision: 0,
                header_type: bus::HeaderType::Standard,
            }),
            Some(DeviceType::Block)
        );
    }

    #[test]
    fn virtio_device_type_invalid() {
        // Non-VirtIO vendor ID.
        assert_eq!(
            virtio_device_type(&DeviceFunctionInfo {
                vendor_id: 0x1234,
                device_id: TRANSITIONAL_BLOCK,
                class: 0,
                subclass: 0,
                prog_if: 0,
                revision: 0,
                header_type: bus::HeaderType::Standard,
            }),
            None
        );

        // Invalid device ID.
        assert_eq!(
            virtio_device_type(&DeviceFunctionInfo {
                vendor_id: VIRTIO_VENDOR_ID,
                device_id: 0x1040,
                class: 0,
                subclass: 0,
                prog_if: 0,
                revision: 0,
                header_type: bus::HeaderType::Standard,
            }),
            None
        );
    }
}
