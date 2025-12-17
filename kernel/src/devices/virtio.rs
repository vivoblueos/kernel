// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
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

use crate::devices::block::init_virtio_block;
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
                        let header =
                            NonNull::new(region.starting_address as *mut VirtIOHeader).unwrap();
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
        let vaddr = unsafe { alloc_zeroed(layout) };
        if vaddr.is_null() {
            handle_alloc_error(layout);
        }
        let paddr = virt_to_phys(vaddr as _);
        let vaddr = NonNull::new(vaddr).unwrap();
        (paddr, vaddr)
    }

    unsafe fn dma_dealloc(_paddr: PhysAddr, vaddr: NonNull<u8>, pages: usize) -> i32 {
        let layout = Layout::from_size_align(pages * PAGE_SIZE, PAGE_SIZE).unwrap();
        dealloc(vaddr.as_ptr(), layout);
        0
    }

    unsafe fn mmio_phys_to_virt(paddr: PhysAddr, _size: usize) -> NonNull<u8> {
        NonNull::new(paddr as _).unwrap()
    }

    unsafe fn share(buffer: NonNull<[u8]>, _direction: BufferDirection) -> PhysAddr {
        let vaddr = buffer.as_ptr() as *mut u8 as usize;
        // Nothing to do
        virt_to_phys(vaddr)
    }

    unsafe fn unshare(_paddr: PhysAddr, _buffer: NonNull<[u8]>, _direction: BufferDirection) {
        // Nothing to do, as the host already has access to all memory and we didn't copy the buffer
        // anywhere else.
    }
}

fn virt_to_phys(vaddr: usize) -> PhysAddr {
    vaddr
}
