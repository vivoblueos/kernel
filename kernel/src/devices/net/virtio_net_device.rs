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

use core::cell::RefCell;

use crate::{
    devices::virtio::{self, VirtioHal},
    net::net_interface::NetInterface,
    time::tick_get_millisecond,
};
use alloc::{boxed::Box, rc::Rc, vec, vec::Vec};
use smoltcp::{
    iface::{Config, Interface, SocketSet},
    phy::{Device, DeviceCapabilities, Medium, RxToken, TxToken},
    time::{Duration, Instant},
    wire::{EthernetAddress, IpAddress, IpCidr, Ipv4Address},
};
use spin::rwlock::RwLock;
use virtio_drivers::{
    device::net::{RxBuffer, VirtIONet},
    transport::SomeTransport,
};

const VIRTIO_NET_BUFFER_SIZE: usize = 65536;
const VIRTIO_NET_QUEUE_SIZE: usize = 16;

static VIRTIO_NET_DEVICES: RwLock<
    Vec<VirtIONet<VirtioHal, SomeTransport<'static>, VIRTIO_NET_QUEUE_SIZE>>,
> = RwLock::new(Vec::new());
type VirtIONetType = VirtIONet<VirtioHal, SomeTransport<'static>, VIRTIO_NET_QUEUE_SIZE>;

pub fn register_virtio_net_device(transport: SomeTransport<'static>) {
    let mut guard = VIRTIO_NET_DEVICES.write();
    guard.push(VirtIONet::new(transport, VIRTIO_NET_BUFFER_SIZE).unwrap());
}

pub fn with_net_device<F, R>(index: usize, f: F) -> Option<R>
where
    F: FnOnce(&mut VirtIONetType) -> R,
{
    let mut guard = VIRTIO_NET_DEVICES.write();
    guard.get_mut(index).map(f)
}

pub fn net_dev_exist() -> bool {
    VIRTIO_NET_DEVICES.read().len() > 0
}

pub struct VirtIONetDevice {
    net_device_index: usize,
}

impl VirtIONetDevice {
    pub fn new(device_index: usize) -> Self {
        Self {
            net_device_index: device_index,
        }
    }
}

impl NetInterface<'_> {
    pub fn create_virtio_device() -> Self {
        let mut inner: VirtIONetDevice = VirtIONetDevice::new(0);
        // Create Device
        let mut socket_set = SocketSet::new(vec![]);

        // Get MAC address from VirtIO device
        let mac_addr = with_net_device(0, |net| net.mac_address())
            .unwrap_or([0x02, 0x00, 0x00, 0x00, 0x00, 0x01]);

        // Create interface
        let mut config = match inner.capabilities().medium {
            Medium::Ethernet => Config::new(EthernetAddress(mac_addr).into()),
            Medium::Ip => Config::new(smoltcp::wire::HardwareAddress::Ip),
            Medium::Ieee802154 => todo!(),
        };

        let mut interface = Interface::new(
            config,
            &mut inner,
            Instant::from_millis(i64::try_from(tick_get_millisecond()).unwrap_or(0)),
        );

        // Configure static guest IP (QEMU user networking)
        interface.update_ip_addrs(|ip_addrs| {
            // TODO config static ip by kconfig
            if ip_addrs
                .push(IpCidr::new(IpAddress::v4(10, 0, 2, 15), 24))
                .is_err()
            {
                log::error!("Add ip addrs to virtio net device fail");
            }
        });

        // Set gateway to reach host
        // In QEMU user networking, the ipv4 gateway is 10.0.2.2
        if interface
            .routes_mut()
            .add_default_ipv4_route(Ipv4Address::new(10, 0, 2, 2))
            .is_err()
        {
            {
                log::error!("Add default ipv4 route to virtio net device fail");
            }
        }

        let device = Rc::new(RefCell::new(
            crate::net::net_interface::NetDevice::VirtioNetDevice(inner),
        ));

        let interface = Rc::new(RefCell::new(interface));
        let socket_set = Rc::new(RefCell::new(socket_set));
        NetInterface::new("VirtIONet".into(), device, interface, socket_set)
    }
}

impl Device for VirtIONetDevice {
    type RxToken<'a>
        = VirtIONetRxToken
    where
        Self: 'a;
    type TxToken<'a>
        = VirtIONetTxToken
    where
        Self: 'a;

    fn receive(&mut self, _timestamp: Instant) -> Option<(Self::RxToken<'_>, Self::TxToken<'_>)> {
        with_net_device(self.net_device_index, |net| {
            if net.can_recv() {
                if let Ok(rx_buf) = net.receive() {
                    return Some((
                        VirtIONetRxToken {
                            device_index: self.net_device_index,
                            buffer: rx_buf,
                        },
                        VirtIONetTxToken {
                            device_index: self.net_device_index,
                        },
                    ));
                }
            }
            None
        })
        .flatten()
    }

    fn transmit(&mut self, _timestamp: Instant) -> Option<Self::TxToken<'_>> {
        with_net_device(self.net_device_index, |net| {
            if net.can_send() {
                Some(VirtIONetTxToken {
                    device_index: self.net_device_index,
                })
            } else {
                None
            }
        })
        .flatten()
    }

    fn capabilities(&self) -> DeviceCapabilities {
        let mut caps = DeviceCapabilities::default();
        caps.max_transmission_unit = 1500;
        caps.max_burst_size = Some(1);
        caps.medium = Medium::Ethernet;
        caps
    }
}

pub struct VirtIONetRxToken {
    device_index: usize,
    buffer: RxBuffer,
}

impl RxToken for VirtIONetRxToken {
    fn consume<R, F>(self, f: F) -> R
    where
        F: FnOnce(&[u8]) -> R,
    {
        let packet = self.buffer.packet();

        let result = f(packet);

        // Recycle rx buffer to ensure virtqueue has space for new packets.
        with_net_device(self.device_index, |net| net.recycle_rx_buffer(self.buffer));
        result
    }
}

pub struct VirtIONetTxToken {
    device_index: usize,
}

impl TxToken for VirtIONetTxToken {
    fn consume<R, F>(self, len: usize, f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R,
    {
        with_net_device(self.device_index, |net| {
            let mut tx_buf = net.new_tx_buffer(len);
            let result = f(tx_buf.packet_mut());
            let _ = net.send(tx_buf);
            result
        })
        .expect("Found no virtio net device!")
    }
}
