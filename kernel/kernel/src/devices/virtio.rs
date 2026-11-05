// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{
    devices::block::init_virtio_block,
    mm::{kernel_phys_to_virt, kernel_virt_to_phys, PhysicalAddress, VirtualAddress},
};
use alloc::alloc::{alloc_zeroed, dealloc, handle_alloc_error};
use core::{alloc::Layout, mem::size_of, ptr::NonNull};
use flat_device_tree::Fdt;
use log::{debug, error, warn};
use virtio_drivers::{
    device::blk::VirtIOBlk,
    transport::{
        mmio::{MmioError, MmioTransport, VirtIOHeader},
        DeviceType, DeviceTypeError, SomeTransport, Transport,
    },
    BufferDirection, Hal, PhysAddr, PAGE_SIZE,
};

use crate::devices::net::virtio_net_device::register_virtio_net_device;

const VIRTIO_MMIO_COMPATIBLE: &str = "virtio,mmio";
pub fn init_virtio(fdt: &Fdt) {
    find_virtio_mmio_devices(fdt);
}
fn find_virtio_mmio_devices(fdt: &Fdt) {
    for node in fdt.all_nodes() {
        if let Some(compatible) = node.compatible() {
            if compatible.all().any(|c| c == VIRTIO_MMIO_COMPATIBLE) {
                debug!("Found VirtIO MMIO device {}", node.name);
                if let Some(region) = node.reg().next() {
                    let region_size = region.size.unwrap_or(0);
                    if region_size < size_of::<VirtIOHeader>() {
                        warn!(
                            "VirtIO MMIO device {} region smaller than VirtIO header size ({} < {})",
                            node.name,
                            region_size,
                            size_of::<VirtIOHeader>()
                        );
                    } else {
                        let header = NonNull::new(
                            kernel_phys_to_virt(PhysicalAddress::new(
                                region.starting_address as usize,
                            ))
                            .into_raw() as *mut VirtIOHeader,
                        )
                        .unwrap();
                        // SAFETY: device tree is correct, VirtIO MMIO devices are mapped.
                        match unsafe { MmioTransport::new(header, region_size) } {
                            Err(MmioError::InvalidDeviceID(
                                DeviceTypeError::InvalidDeviceType(0),
                            )) => {
                                warn!("Ignoring VirtIO device with zero device ID.");
                            }
                            Err(e) => {
                                warn!("Error creating VirtIO transport: {}", e);
                            }
                            Ok(mut transport) => {
                                debug!(
                                    "Detected virtio MMIO device with device type {:?}, vendor ID {:#x}, version {:?}, features {:#018x}",
                                    transport.device_type(),
                                    transport.vendor_id(),
                                    transport.version(),
                                    transport.read_device_features(),
                                );
                                init_virtio_device(transport.into());
                            }
                        }
                    }
                } else {
                    warn!("VirtIO MMIO device {} missing region", node.name);
                }
            }
        }
    }
}

fn init_virtio_device(transport: SomeTransport<'static>) {
    match transport.device_type() {
        DeviceType::Network => {
            crate::devices::net::virtio_net_device::register_virtio_net_device(transport);
        }
        DeviceType::Block => {
            if let Err(e) = init_virtio_block(VirtIOBlk::new(transport).unwrap()) {
                error!("Failed to init virtio blk, {:?}", e);
            }
        }
        t => {
            debug!("Ignoring unsupported VirtIO device type {:?}", t);
        }
    }
}

#[derive(Debug)]
pub struct VirtioHal;

// SAFETY: VirtIO MMIO devices are mapped.
unsafe impl Hal for VirtioHal {
    fn dma_alloc(pages: usize, _direction: BufferDirection) -> (PhysAddr, NonNull<u8>) {
        debug_assert!(pages > 0);
        let layout = Layout::from_size_align(pages * PAGE_SIZE, PAGE_SIZE).unwrap();
        #[cfg(paging)]
        {
            let physical = crate::mm::paging::first_fit::FirstFitFrameAllocator::instance()
                .alloc_frames(pages)
                .unwrap_or_else(|| handle_alloc_error(layout));
            let ptr = kernel_phys_to_virt(physical).into_raw() as *mut u8;
            unsafe {
                ptr.write_bytes(0, layout.size());
            }
            (physical.into_raw(), NonNull::new(ptr).unwrap())
        }
        #[cfg(not(paging))]
        {
            let vaddr = unsafe { alloc_zeroed(layout) };
            if vaddr.is_null() {
                handle_alloc_error(layout);
            }
            let paddr = kernel_virt_to_phys(VirtualAddress::new(vaddr as usize)).into_raw();
            (paddr, NonNull::new(vaddr).unwrap())
        }
    }

    unsafe fn dma_dealloc(paddr: PhysAddr, vaddr: NonNull<u8>, pages: usize) -> i32 {
        #[cfg(paging)]
        crate::mm::paging::first_fit::FirstFitFrameAllocator::instance()
            .free_frames(PhysicalAddress::new(paddr), pages)
            .expect("release DMA pages");
        #[cfg(not(paging))]
        dealloc(
            vaddr.as_ptr(),
            Layout::from_size_align(pages * PAGE_SIZE, PAGE_SIZE).unwrap(),
        );
        0
    }

    unsafe fn mmio_phys_to_virt(paddr: PhysAddr, _size: usize) -> NonNull<u8> {
        NonNull::new(kernel_phys_to_virt(PhysicalAddress::new(paddr)).into_raw() as *mut u8)
            .unwrap()
    }

    unsafe fn share(buffer: NonNull<[u8]>, direction: BufferDirection) -> PhysAddr {
        #[cfg(paging)]
        {
            let len = buffer.len();
            if len == 0 {
                return 0;
            }
            let (physical, bounce) = Self::dma_alloc(len.div_ceil(PAGE_SIZE), direction);
            if direction != BufferDirection::DeviceToDriver {
                core::ptr::copy_nonoverlapping(buffer.as_ptr() as *const u8, bounce.as_ptr(), len);
            }
            physical
        }
        #[cfg(not(paging))]
        kernel_virt_to_phys(VirtualAddress::new(buffer.as_ptr() as *mut u8 as usize)).into_raw()
    }

    unsafe fn unshare(paddr: PhysAddr, buffer: NonNull<[u8]>, direction: BufferDirection) {
        #[cfg(paging)]
        {
            let len = buffer.len();
            if len == 0 {
                return;
            }
            let bounce = NonNull::new(
                kernel_phys_to_virt(PhysicalAddress::new(paddr)).into_raw() as *mut u8
            )
            .unwrap();
            if direction != BufferDirection::DriverToDevice {
                core::ptr::copy_nonoverlapping(bounce.as_ptr(), buffer.as_ptr() as *mut u8, len);
            }
            Self::dma_dealloc(paddr, bounce, len.div_ceil(PAGE_SIZE));
        }
    }
}

#[cfg(all(test, paging))]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn dma_allocations_keep_contiguous_physical_backing() {
        let (physical, virtual_start) = VirtioHal::dma_alloc(3, BufferDirection::Both);
        for offset in (0..3 * PAGE_SIZE).step_by(PAGE_SIZE) {
            assert_eq!(
                kernel_virt_to_phys(VirtualAddress::new(
                    virtual_start.as_ptr() as usize + offset
                ))
                .into_raw(),
                physical + offset
            );
        }
        let bytes = unsafe { core::slice::from_raw_parts(virtual_start.as_ptr(), 3 * PAGE_SIZE) };
        assert!(bytes.iter().all(|b| *b == 0));
        unsafe { VirtioHal::dma_dealloc(physical, virtual_start, 3) };
    }

    #[test]
    fn dma_sharing_copies_only_in_the_requested_direction() {
        for direction in [
            BufferDirection::DriverToDevice,
            BufferDirection::DeviceToDriver,
            BufferDirection::Both,
        ] {
            let mut original = alloc::vec![0x2au8;PAGE_SIZE+17];
            let buffer = NonNull::from(original.as_mut_slice());
            let physical = unsafe { VirtioHal::share(buffer, direction) };
            let bounce = kernel_phys_to_virt(PhysicalAddress::new(physical)).into_raw() as *mut u8;
            let bytes = unsafe { core::slice::from_raw_parts_mut(bounce, original.len()) };
            let input = if direction == BufferDirection::DeviceToDriver {
                0
            } else {
                0x2a
            };
            assert!(bytes.iter().all(|b| *b == input));
            bytes.fill(0x73);
            unsafe { VirtioHal::unshare(physical, buffer, direction) };
            let output = if direction == BufferDirection::DriverToDevice {
                0x2a
            } else {
                0x73
            };
            assert!(original.iter().all(|b| *b == output));
        }
    }
}
