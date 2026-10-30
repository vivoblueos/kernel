//! Driver for VirtIO network devices.

#[cfg(feature = "alloc")]
mod dev;
mod dev_raw;
#[cfg(feature = "alloc")]
mod net_buf;

pub use self::dev_raw::VirtIONetRaw;
#[cfg(feature = "alloc")]
pub use self::{dev::VirtIONet, net_buf::RxBuffer, net_buf::TxBuffer};

use crate::config::ReadOnly;
use bitflags::bitflags;
use zerocopy::{FromBytes, Immutable, IntoBytes, KnownLayout};

const MAX_BUFFER_LEN: usize = 65535;
const MIN_BUFFER_LEN: usize = 1526;
const NET_HDR_SIZE: usize = core::mem::size_of::<VirtioNetHdr>();

bitflags! {
    #[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
    struct Features: u64 {
        /// Device handles packets with partial checksum.
        /// This "checksum offload" is a common feature on modern network cards.
        const CSUM = 1 << 0;
        /// Driver handles packets with partial checksum.
        const GUEST_CSUM = 1 << 1;
        /// Control channel offloads reconfiguration support.
        const CTRL_GUEST_OFFLOADS = 1 << 2;
        /// Device maximum MTU reporting is supported.
        ///
        /// If offered by the device, device advises driver about the value of
        /// its maximum MTU. If negotiated, the driver uses mtu as the maximum
        /// MTU value.
        const MTU = 1 << 3;
        /// Device has given MAC address.
        const MAC = 1 << 5;
        /// Device handles packets with any GSO type. (legacy)
        const GSO = 1 << 6;
        /// Driver can receive TSOv4.
        const GUEST_TSO4 = 1 << 7;
        /// Driver can receive TSOv6.
        const GUEST_TSO6 = 1 << 8;
        /// Driver can receive TSO with ECN.
        const GUEST_ECN = 1 << 9;
        /// Driver can receive UFO.
        const GUEST_UFO = 1 << 10;
        /// Device can receive TSOv4.
        const HOST_TSO4 = 1 << 11;
        /// Device can receive TSOv6.
        const HOST_TSO6 = 1 << 12;
        /// Device can receive TSO with ECN.
        const HOST_ECN = 1 << 13;
        /// Device can receive UFO.
        const HOST_UFO = 1 << 14;
        /// Driver can merge receive buffers.
        const MRG_RXBUF = 1 << 15;
        /// Configuration status field is available.
        const STATUS = 1 << 16;
        /// Control channel is available.
        const CTRL_VQ = 1 << 17;
        /// Control channel RX mode support.
        const CTRL_RX = 1 << 18;
        /// Control channel VLAN filtering.
        const CTRL_VLAN = 1 << 19;
        /// Device supports VIRTIO_NET_CTRL_RX_ALLUNI, VIRTIO_NET_CTRL_RX_NOMULTI,
        /// VIRTIO_NET_CTRL_RX_NOUNI and VIRTIO_NET_CTRL_RX_NOBCAST.
        const CTRL_RX_EXTRA = 1 << 20;
        /// Driver can send gratuitous packets.
        const GUEST_ANNOUNCE = 1 << 21;
        /// Device supports multiqueue with automatic receive steering.
        const MQ = 1 << 22;
        /// Set MAC address through control channel.
        const CTL_MAC_ADDR = 1 << 23;

        // device independent
        const RING_INDIRECT_DESC = 1 << 28;
        const RING_EVENT_IDX = 1 << 29;
        const VERSION_1 = 1 << 32; // legacy
    }
}

#[derive(
    Copy, Clone, Debug, Default, Eq, FromBytes, Immutable, IntoBytes, KnownLayout, PartialEq,
)]
#[repr(transparent)]
struct Status(u16);

bitflags! {
    impl Status: u16 {
        const LINK_UP = 1;
        const ANNOUNCE = 2;
    }
}

bitflags! {
    #[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
    struct InterruptStatus : u32 {
        const USED_RING_UPDATE = 1 << 0;
        const CONFIGURATION_CHANGE = 1 << 1;
    }
}

#[repr(C)]
struct Config {
    mac: ReadOnly<EthernetAddress>,
    status: ReadOnly<Status>,
    max_virtqueue_pairs: ReadOnly<u16>,
    mtu: ReadOnly<u16>,
}

type EthernetAddress = [u8; 6];

/// VirtIO 5.1.6 Device Operation:
///
/// Packets are transmitted by placing them in the transmitq1. . .transmitqN,
/// and buffers for incoming packets are placed in the receiveq1. . .receiveqN.
/// In each case, the packet itself is preceded by a header.
#[repr(C)]
#[derive(Debug, Default, FromBytes, Immutable, IntoBytes, KnownLayout)]
pub struct VirtioNetHdr {
    flags: Flags,
    gso_type: GsoType,
    hdr_len: u16, // cannot rely on this
    gso_size: u16,
    csum_start: u16,
    csum_offset: u16,
    // num_buffers: u16, // only available when the feature MRG_RXBUF is negotiated.
    // payload starts from here
}

#[derive(
    IntoBytes, Copy, Clone, Debug, Default, Eq, FromBytes, Immutable, KnownLayout, PartialEq,
)]
#[repr(transparent)]
struct Flags(u8);

bitflags! {
    impl Flags: u8 {
        const NEEDS_CSUM = 1;
        const DATA_VALID = 2;
        const RSC_INFO   = 4;
    }
}

#[repr(transparent)]
#[derive(
    IntoBytes, Debug, Copy, Clone, Default, Eq, FromBytes, Immutable, KnownLayout, PartialEq,
)]
struct GsoType(u8);

impl GsoType {
    const NONE: GsoType = GsoType(0);
    const TCPV4: GsoType = GsoType(1);
    const UDP: GsoType = GsoType(3);
    const TCPV6: GsoType = GsoType(4);
    const ECN: GsoType = GsoType(0x80);
}

const QUEUE_RECEIVE: u16 = 0;
const QUEUE_TRANSMIT: u16 = 1;
const SUPPORTED_FEATURES: Features = Features::MAC
    .union(Features::STATUS)
    .union(Features::RING_EVENT_IDX)
    .union(Features::RING_INDIRECT_DESC);
