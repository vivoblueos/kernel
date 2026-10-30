//! MMIO transport for VirtIO.

use super::{DeviceStatus, DeviceType, DeviceTypeError, Transport};
use crate::{align_up, queue::Descriptor, Error, PhysAddr, PAGE_SIZE};
use core::{
    convert::{TryFrom, TryInto},
    mem::{align_of, size_of},
    ops::Deref,
    ptr::NonNull,
};
use safe_mmio::{
    field, field_shared,
    fields::{ReadPure, ReadPureWrite, WriteOnly},
    UniqueMmioPointer,
};
use zerocopy::{FromBytes, Immutable, IntoBytes};

const MAGIC_VALUE: u32 = 0x7472_6976;
pub(crate) const LEGACY_VERSION: u32 = 1;
pub(crate) const MODERN_VERSION: u32 = 2;
const CONFIG_SPACE_OFFSET: usize = 0x100;

/// The version of the VirtIO MMIO transport supported by a device.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
#[repr(u32)]
pub enum MmioVersion {
    /// Legacy MMIO transport with page-based addressing.
    Legacy = LEGACY_VERSION,
    /// Modern MMIO transport.
    Modern = MODERN_VERSION,
}

impl TryFrom<u32> for MmioVersion {
    type Error = MmioError;

    fn try_from(version: u32) -> Result<Self, Self::Error> {
        match version {
            LEGACY_VERSION => Ok(Self::Legacy),
            MODERN_VERSION => Ok(Self::Modern),
            _ => Err(MmioError::UnsupportedVersion(version)),
        }
    }
}

impl From<MmioVersion> for u32 {
    fn from(version: MmioVersion) -> Self {
        match version {
            MmioVersion::Legacy => LEGACY_VERSION,
            MmioVersion::Modern => MODERN_VERSION,
        }
    }
}

/// An error encountered initialising a VirtIO MMIO transport.
#[derive(Clone, Debug, Eq, Error, PartialEq)]
pub enum MmioError {
    /// The header doesn't start with the expected magic value 0x74726976.
    #[error("Invalid magic value {0:#010x} (expected 0x74726976)")]
    BadMagic(u32),
    /// The header reports a version number that is neither 1 (legacy) nor 2 (modern).
    #[error("Unsupported Virtio MMIO version {0}")]
    UnsupportedVersion(u32),
    /// The header reports a device ID of 0.
    #[error("Invalid or unknown device ID: {0}")]
    InvalidDeviceID(DeviceTypeError),
    /// The MMIO region size was smaller than the header size we expect.
    #[error("MMIO region too small")]
    MmioRegionTooSmall,
}

/// MMIO Device Register Interface, both legacy and modern.
///
/// Ref: 4.2.2 MMIO Device Register Layout and 4.2.4 Legacy interface
#[derive(Debug)]
#[repr(C)]
pub struct VirtIOHeader {
    /// Magic value
    magic: ReadPure<u32>,

    /// Device version number
    ///
    /// Legacy device returns value 0x1.
    version: ReadPure<u32>,

    /// Virtio Subsystem Device ID
    device_id: ReadPure<u32>,

    /// Virtio Subsystem Vendor ID
    vendor_id: ReadPure<u32>,

    /// Flags representing features the device supports
    device_features: ReadPure<u32>,

    /// Device (host) features word selection
    device_features_sel: WriteOnly<u32>,

    /// Reserved
    __r1: [u32; 2],

    /// Flags representing device features understood and activated by the driver
    driver_features: WriteOnly<u32>,

    /// Activated (guest) features word selection
    driver_features_sel: WriteOnly<u32>,

    /// Guest page size
    ///
    /// The driver writes the guest page size in bytes to the register during
    /// initialization, before any queues are used. This value should be a
    /// power of 2 and is used by the device to calculate the Guest address
    /// of the first queue page (see QueuePFN).
    legacy_guest_page_size: WriteOnly<u32>,

    /// Reserved
    __r2: u32,

    /// Virtual queue index
    ///
    /// Writing to this register selects the virtual queue that the following
    /// operations on the QueueNumMax, QueueNum, QueueAlign and QueuePFN
    /// registers apply to. The index number of the first queue is zero (0x0).
    queue_sel: WriteOnly<u32>,

    /// Maximum virtual queue size
    ///
    /// Reading from the register returns the maximum size of the queue the
    /// device is ready to process or zero (0x0) if the queue is not available.
    /// This applies to the queue selected by writing to QueueSel and is
    /// allowed only when QueuePFN is set to zero (0x0), so when the queue is
    /// not actively used.
    queue_num_max: ReadPure<u32>,

    /// Virtual queue size
    ///
    /// Queue size is the number of elements in the queue. Writing to this
    /// register notifies the device what size of the queue the driver will use.
    /// This applies to the queue selected by writing to QueueSel.
    queue_num: WriteOnly<u32>,

    /// Used Ring alignment in the virtual queue
    ///
    /// Writing to this register notifies the device about alignment boundary
    /// of the Used Ring in bytes. This value should be a power of 2 and
    /// applies to the queue selected by writing to QueueSel.
    legacy_queue_align: WriteOnly<u32>,

    /// Guest physical page number of the virtual queue
    ///
    /// Writing to this register notifies the device about location of the
    /// virtual queue in the Guest’s physical address space. This value is
    /// the index number of a page starting with the queue Descriptor Table.
    /// Value zero (0x0) means physical address zero (0x00000000) and is illegal.
    /// When the driver stops using the queue it writes zero (0x0) to this
    /// register. Reading from this register returns the currently used page
    /// number of the queue, therefore a value other than zero (0x0) means that
    /// the queue is in use. Both read and write accesses apply to the queue
    /// selected by writing to QueueSel.
    legacy_queue_pfn: ReadPureWrite<u32>,

    /// new interface only
    queue_ready: ReadPureWrite<u32>,

    /// Reserved
    __r3: [u32; 2],

    /// Queue notifier
    queue_notify: WriteOnly<u32>,

    /// Reserved
    __r4: [u32; 3],

    /// Interrupt status
    interrupt_status: ReadPure<u32>,

    /// Interrupt acknowledge
    interrupt_ack: WriteOnly<u32>,

    /// Reserved
    __r5: [u32; 2],

    /// Device status
    ///
    /// Reading from this register returns the current device status flags.
    /// Writing non-zero values to this register sets the status flags,
    /// indicating the OS/driver progress. Writing zero (0x0) to this register
    /// triggers a device reset. The device sets QueuePFN to zero (0x0) for
    /// all queues in the device. Also see 3.1 Device Initialization.
    status: ReadPureWrite<DeviceStatus>,

    /// Reserved
    __r6: [u32; 3],

    // new interface only since here
    queue_desc_low: WriteOnly<u32>,
    queue_desc_high: WriteOnly<u32>,

    /// Reserved
    __r7: [u32; 2],

    queue_driver_low: WriteOnly<u32>,
    queue_driver_high: WriteOnly<u32>,

    /// Reserved
    __r8: [u32; 2],

    queue_device_low: WriteOnly<u32>,
    queue_device_high: WriteOnly<u32>,

    /// Reserved
    __r9: [u32; 21],

    config_generation: ReadPure<u32>,
}

impl VirtIOHeader {
    /// Constructs a fake VirtIO header for use in unit tests.
    #[cfg(test)]
    pub fn make_fake_header(
        version: u32,
        device_id: u32,
        vendor_id: u32,
        device_features: u32,
        queue_num_max: u32,
    ) -> Self {
        Self {
            magic: ReadPure(MAGIC_VALUE),
            version: ReadPure(version),
            device_id: ReadPure(device_id),
            vendor_id: ReadPure(vendor_id),
            device_features: ReadPure(device_features),
            device_features_sel: WriteOnly::default(),
            __r1: Default::default(),
            driver_features: Default::default(),
            driver_features_sel: Default::default(),
            legacy_guest_page_size: Default::default(),
            __r2: Default::default(),
            queue_sel: Default::default(),
            queue_num_max: ReadPure(queue_num_max),
            queue_num: Default::default(),
            legacy_queue_align: Default::default(),
            legacy_queue_pfn: Default::default(),
            queue_ready: Default::default(),
            __r3: Default::default(),
            queue_notify: Default::default(),
            __r4: Default::default(),
            interrupt_status: Default::default(),
            interrupt_ack: Default::default(),
            __r5: Default::default(),
            status: ReadPureWrite(DeviceStatus::empty()),
            __r6: Default::default(),
            queue_desc_low: Default::default(),
            queue_desc_high: Default::default(),
            __r7: Default::default(),
            queue_driver_low: Default::default(),
            queue_driver_high: Default::default(),
            __r8: Default::default(),
            queue_device_low: Default::default(),
            queue_device_high: Default::default(),
            __r9: Default::default(),
            config_generation: Default::default(),
        }
    }
}

/// MMIO Device Register Interface.
///
/// Ref: 4.2.2 MMIO Device Register Layout and 4.2.4 Legacy interface
#[derive(Debug)]
pub struct MmioTransport<'a> {
    header: UniqueMmioPointer<'a, VirtIOHeader>,
    config_space: UniqueMmioPointer<'a, [u8]>,
    version: MmioVersion,
    device_type: DeviceType,
}

impl<'a> MmioTransport<'a> {
    /// Constructs a new VirtIO MMIO transport, or returns an error if the header reports an
    /// unsupported version.
    ///
    /// # Safety
    ///
    /// `header` must point to a properly aligned valid VirtIO MMIO region, which must remain valid
    /// for the lifetime `'a`. This includes the config space following the header, if any.
    pub unsafe fn new(header: NonNull<VirtIOHeader>, mmio_size: usize) -> Result<Self, MmioError> {
        let Some(config_space_size) = mmio_size.checked_sub(CONFIG_SPACE_OFFSET) else {
            return Err(MmioError::MmioRegionTooSmall);
        };
        let config_space = NonNull::slice_from_raw_parts(
            header.cast::<u8>().byte_add(CONFIG_SPACE_OFFSET),
            config_space_size,
        );
        // SAFETY: The caller promises that the config space following the header is an MMIO region
        // valid for `'a`.
        let config_space = unsafe { UniqueMmioPointer::new(config_space) };

        // SAFETY: The caller promises that `header` is a properly aligned MMIO region  valid for
        // `'a`.
        let header = UniqueMmioPointer::new(header);

        Self::new_from_unique(header, config_space)
    }

    /// Constructs a new VirtIO MMIO transport, or returns an error if the header reports an
    /// unsupported version.
    pub fn new_from_unique(
        header: UniqueMmioPointer<'a, VirtIOHeader>,
        config_space: UniqueMmioPointer<'a, [u8]>,
    ) -> Result<Self, MmioError> {
        let magic = field_shared!(header, magic).read();
        if magic != MAGIC_VALUE {
            return Err(MmioError::BadMagic(magic));
        }
        let device_id = field_shared!(header, device_id).read();
        let device_type = DeviceType::try_from(device_id).map_err(MmioError::InvalidDeviceID)?;
        let version = field_shared!(header, version).read().try_into()?;
        Ok(Self {
            header,
            version,
            device_type,
            config_space,
        })
    }

    /// Gets the version of the VirtIO MMIO transport.
    pub fn version(&self) -> MmioVersion {
        self.version
    }

    /// Gets the vendor ID.
    pub fn vendor_id(&self) -> u32 {
        field_shared!(self.header, vendor_id).read()
    }
}

// SAFETY: `&MmioTransport` only allows MMIO reads or getting the config space, both of which are
// fine to happen concurrently on different CPU cores.
unsafe impl Sync for MmioTransport<'_> {}

impl Transport for MmioTransport<'_> {
    fn device_type(&self) -> DeviceType {
        self.device_type
    }

    fn read_device_features(&mut self) -> u64 {
        field!(self.header, device_features_sel).write(0); // device features [0, 32)
        let mut device_features_bits = field_shared!(self.header, device_features).read().into();
        field!(self.header, device_features_sel).write(1); // device features [32, 64)
        device_features_bits += (field_shared!(self.header, device_features).read() as u64) << 32;
        device_features_bits
    }

    fn write_driver_features(&mut self, driver_features: u64) {
        field!(self.header, driver_features_sel).write(0); // driver features [0, 32)
        field!(self.header, driver_features).write(driver_features as u32);
        field!(self.header, driver_features_sel).write(1); // driver features [32, 64)
        field!(self.header, driver_features).write((driver_features >> 32) as u32);
    }

    fn max_queue_size(&mut self, queue: u16) -> u32 {
        field!(self.header, queue_sel).write(queue.into());
        field_shared!(self.header, queue_num_max).read()
    }

    fn notify(&mut self, queue: u16) {
        field!(self.header, queue_notify).write(queue.into());
    }

    fn get_status(&self) -> DeviceStatus {
        field_shared!(self.header, status).read()
    }

    fn set_status(&mut self, status: DeviceStatus) {
        field!(self.header, status).write(status);
    }

    fn set_guest_page_size(&mut self, guest_page_size: u32) {
        match self.version {
            MmioVersion::Legacy => {
                field!(self.header, legacy_guest_page_size).write(guest_page_size);
            }
            MmioVersion::Modern => {
                // No-op, modern devices don't care.
            }
        }
    }

    fn requires_legacy_layout(&self) -> bool {
        match self.version {
            MmioVersion::Legacy => true,
            MmioVersion::Modern => false,
        }
    }

    fn queue_set(
        &mut self,
        queue: u16,
        size: u32,
        descriptors: PhysAddr,
        driver_area: PhysAddr,
        device_area: PhysAddr,
    ) {
        match self.version {
            MmioVersion::Legacy => {
                assert_eq!(
                    driver_area - descriptors,
                    size_of::<Descriptor>() * size as usize
                );
                assert_eq!(
                    device_area - descriptors,
                    align_up(
                        size_of::<Descriptor>() * size as usize
                            + size_of::<u16>() * (size as usize + 3)
                    )
                );
                let align = PAGE_SIZE as u32;
                let pfn = (descriptors / PAGE_SIZE) as u32;
                assert_eq!(pfn as usize * PAGE_SIZE, descriptors);
                field!(self.header, queue_sel).write(queue.into());
                field!(self.header, queue_num).write(size);
                field!(self.header, legacy_queue_align).write(align);
                field!(self.header, legacy_queue_pfn).write(pfn);
            }
            MmioVersion::Modern => {
                field!(self.header, queue_sel).write(queue.into());
                field!(self.header, queue_num).write(size);
                field!(self.header, queue_desc_low).write(descriptors as u32);
                field!(self.header, queue_desc_high).write((descriptors >> 32) as u32);
                field!(self.header, queue_driver_low).write(driver_area as u32);
                field!(self.header, queue_driver_high).write((driver_area >> 32) as u32);
                field!(self.header, queue_device_low).write(device_area as u32);
                field!(self.header, queue_device_high).write((device_area >> 32) as u32);
                field!(self.header, queue_ready).write(1);
            }
        }
    }

    fn queue_unset(&mut self, queue: u16) {
        match self.version {
            MmioVersion::Legacy => {
                field!(self.header, queue_sel).write(queue.into());
                field!(self.header, queue_num).write(0);
                field!(self.header, legacy_queue_align).write(0);
                field!(self.header, legacy_queue_pfn).write(0);
            }
            MmioVersion::Modern => {
                field!(self.header, queue_sel).write(queue.into());

                field!(self.header, queue_ready).write(0);
                // Wait until we read the same value back, to ensure synchronisation (see 4.2.2.2).
                let queue_ready = field_shared!(self.header, queue_ready);
                while queue_ready.read() != 0 {}

                field!(self.header, queue_num).write(0);
                field!(self.header, queue_desc_low).write(0);
                field!(self.header, queue_desc_high).write(0);
                field!(self.header, queue_driver_low).write(0);
                field!(self.header, queue_driver_high).write(0);
                field!(self.header, queue_device_low).write(0);
                field!(self.header, queue_device_high).write(0);
            }
        }
    }

    fn queue_used(&mut self, queue: u16) -> bool {
        field!(self.header, queue_sel).write(queue.into());
        match self.version {
            MmioVersion::Legacy => field_shared!(self.header, legacy_queue_pfn).read() != 0,
            MmioVersion::Modern => field_shared!(self.header, queue_ready).read() != 0,
        }
    }

    fn ack_interrupt(&mut self) -> bool {
        let interrupt = field_shared!(self.header, interrupt_status).read();
        if interrupt != 0 {
            field!(self.header, interrupt_ack).write(interrupt);
            true
        } else {
            false
        }
    }

    fn read_config_generation(&self) -> u32 {
        field_shared!(self.header, config_generation).read()
    }

    fn read_config_space<T: FromBytes + IntoBytes>(&self, offset: usize) -> Result<T, Error> {
        assert!(align_of::<T>() <= 4,
            "Driver expected config space alignment of {} bytes, but VirtIO only guarantees 4 byte alignment.",
            align_of::<T>());
        assert!(offset % align_of::<T>() == 0);

        if self.config_space.len() < offset + size_of::<T>() {
            Err(Error::ConfigSpaceTooSmall)
        } else {
            // SAFETY: The caller of `MmioTransport::new` guaranteed that the header pointer was
            // valid, including the config space. We have checked that the value is properly aligned
            // for `T` and within the bounds of the config space. Reading the config space shouldn't
            // have side-effects.
            unsafe {
                let ptr = self.config_space.ptr().cast::<T>().byte_add(offset);
                Ok(self
                    .config_space
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
        assert!(offset % align_of::<T>() == 0);

        if self.config_space.len() < offset + size_of::<T>() {
            Err(Error::ConfigSpaceTooSmall)
        } else {
            // SAFETY: The caller of `MmioTransport::new` guaranteed that the header pointer was
            // valid, including the config space. We have checked that the value is properly aligned
            // for `T` and within the bounds of the config space.
            unsafe {
                let ptr = self.config_space.ptr_nonnull().cast::<T>().byte_add(offset);
                self.config_space.child(ptr).write_unsafe(value);
            }
            Ok(())
        }
    }
}

impl Drop for MmioTransport<'_> {
    fn drop(&mut self) {
        // Reset the device when the transport is dropped.
        self.set_status(DeviceStatus::empty())
    }
}
