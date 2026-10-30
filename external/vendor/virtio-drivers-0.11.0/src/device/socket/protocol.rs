//! This module defines the socket device protocol according to the virtio spec v1.1 5.10 Socket Device

use super::error::{self, SocketError};
use crate::config::ReadOnly;
use bitflags::bitflags;
use core::{
    convert::{TryFrom, TryInto},
    fmt,
};
use zerocopy::{
    byteorder::{LittleEndian, U16, U32, U64},
    FromBytes, Immutable, IntoBytes, KnownLayout,
};

/// Well-known CID for the host.
pub const VMADDR_CID_HOST: u64 = 2;

/// Currently only stream sockets are supported. type is 1 for stream socket types.
#[derive(Copy, Clone, Debug)]
#[repr(u16)]
pub enum SocketType {
    /// Stream sockets provide in-order, guaranteed, connection-oriented delivery without message boundaries.
    Stream = 1,
    /// seqpacket socket type introduced in virtio-v1.2.
    SeqPacket = 2,
}

impl From<SocketType> for U16<LittleEndian> {
    fn from(socket_type: SocketType) -> Self {
        (socket_type as u16).into()
    }
}

/// VirtioVsockConfig is the vsock device configuration space.
#[derive(FromBytes, Immutable, IntoBytes)]
#[repr(C)]
pub struct VirtioVsockConfig {
    /// The guest_cid field contains the guest’s context ID, which uniquely identifies
    /// the device for its lifetime. The upper 32 bits of the CID are reserved and zeroed.
    ///
    /// According to virtio spec v1.1 2.4.1 Driver Requirements: Device Configuration Space,
    /// drivers MUST NOT assume reads from fields greater than 32 bits wide are atomic.
    /// So we need to split the u64 guest_cid into two parts.
    pub guest_cid_low: ReadOnly<u32>,
    pub guest_cid_high: ReadOnly<u32>,
}

/// The message header for data packets sent on the tx/rx queues
#[repr(C, packed)]
#[derive(Clone, Copy, Debug, Eq, FromBytes, Immutable, IntoBytes, KnownLayout, PartialEq)]
pub struct VirtioVsockHdr {
    pub src_cid: U64<LittleEndian>,
    pub dst_cid: U64<LittleEndian>,
    pub src_port: U32<LittleEndian>,
    pub dst_port: U32<LittleEndian>,
    pub len: U32<LittleEndian>,
    pub socket_type: U16<LittleEndian>,
    pub op: U16<LittleEndian>,
    pub flags: U32<LittleEndian>,
    /// Total receive buffer space for this socket. This includes both free and in-use buffers.
    pub buf_alloc: U32<LittleEndian>,
    /// Free-running bytes received counter.
    pub fwd_cnt: U32<LittleEndian>,
}

impl Default for VirtioVsockHdr {
    fn default() -> Self {
        Self {
            src_cid: 0.into(),
            dst_cid: 0.into(),
            src_port: 0.into(),
            dst_port: 0.into(),
            len: 0.into(),
            socket_type: SocketType::Stream.into(),
            op: 0.into(),
            flags: 0.into(),
            buf_alloc: 0.into(),
            fwd_cnt: 0.into(),
        }
    }
}

impl VirtioVsockHdr {
    /// Returns the length of the data.
    pub fn len(&self) -> u32 {
        u32::from(self.len)
    }

    pub fn op(&self) -> error::Result<VirtioVsockOp> {
        self.op.try_into()
    }

    pub fn source(&self) -> VsockAddr {
        VsockAddr {
            cid: self.src_cid.get(),
            port: self.src_port.get(),
        }
    }

    pub fn destination(&self) -> VsockAddr {
        VsockAddr {
            cid: self.dst_cid.get(),
            port: self.dst_port.get(),
        }
    }

    pub fn check_data_is_empty(&self) -> error::Result<()> {
        if self.len() == 0 {
            Ok(())
        } else {
            Err(SocketError::UnexpectedDataInPacket)
        }
    }
}

/// Socket address.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub struct VsockAddr {
    /// Context Identifier.
    pub cid: u64,
    /// Port number.
    pub port: u32,
}

/// An event sent to the event queue
#[derive(Copy, Clone, Debug, Default, IntoBytes, FromBytes, Immutable, KnownLayout)]
#[repr(C)]
pub struct VirtioVsockEvent {
    // ID from the virtio_vsock_event_id struct in the virtio spec
    pub id: U32<LittleEndian>,
}

#[derive(Copy, Clone, Eq, PartialEq)]
#[repr(u16)]
pub enum VirtioVsockOp {
    Invalid = 0,

    /* Connect operations */
    Request = 1,
    Response = 2,
    Rst = 3,
    Shutdown = 4,

    /* To send payload */
    Rw = 5,

    /* Tell the peer our credit info */
    CreditUpdate = 6,
    /* Request the peer to send the credit info to us */
    CreditRequest = 7,
}

impl From<VirtioVsockOp> for U16<LittleEndian> {
    fn from(op: VirtioVsockOp) -> Self {
        (op as u16).into()
    }
}

impl TryFrom<U16<LittleEndian>> for VirtioVsockOp {
    type Error = SocketError;

    fn try_from(v: U16<LittleEndian>) -> Result<Self, Self::Error> {
        let op = match u16::from(v) {
            0 => Self::Invalid,
            1 => Self::Request,
            2 => Self::Response,
            3 => Self::Rst,
            4 => Self::Shutdown,
            5 => Self::Rw,
            6 => Self::CreditUpdate,
            7 => Self::CreditRequest,
            _ => return Err(SocketError::UnknownOperation(v.into())),
        };
        Ok(op)
    }
}

impl fmt::Debug for VirtioVsockOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Invalid => write!(f, "VIRTIO_VSOCK_OP_INVALID"),
            Self::Request => write!(f, "VIRTIO_VSOCK_OP_REQUEST"),
            Self::Response => write!(f, "VIRTIO_VSOCK_OP_RESPONSE"),
            Self::Rst => write!(f, "VIRTIO_VSOCK_OP_RST"),
            Self::Shutdown => write!(f, "VIRTIO_VSOCK_OP_SHUTDOWN"),
            Self::Rw => write!(f, "VIRTIO_VSOCK_OP_RW"),
            Self::CreditUpdate => write!(f, "VIRTIO_VSOCK_OP_CREDIT_UPDATE"),
            Self::CreditRequest => write!(f, "VIRTIO_VSOCK_OP_CREDIT_REQUEST"),
        }
    }
}

bitflags! {
    #[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
    pub(crate) struct Feature: u64 {
        /// stream socket type is supported.
        const STREAM = 1 << 0;
        /// seqpacket socket type is supported.
        const SEQ_PACKET = 1 << 1;

        // device independent
        const NOTIFY_ON_EMPTY       = 1 << 24; // legacy
        const ANY_LAYOUT            = 1 << 27; // legacy
        const RING_INDIRECT_DESC    = 1 << 28;
        const RING_EVENT_IDX        = 1 << 29;
        const UNUSED                = 1 << 30; // legacy
        const VERSION_1             = 1 << 32; // detect legacy

        // since virtio v1.1
        const ACCESS_PLATFORM       = 1 << 33;
        const RING_PACKED           = 1 << 34;
        const IN_ORDER              = 1 << 35;
        const ORDER_PLATFORM        = 1 << 36;
        const SR_IOV                = 1 << 37;
        const NOTIFICATION_DATA     = 1 << 38;
    }
}

bitflags! {
    /// Flags sent with a shutdown request to hint that the peer won't send or receive more data.
    #[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
    pub struct StreamShutdown: u32 {
        /// The peer will not receive any more data.
        const RECEIVE = 1 << 0;
        /// The peer will not send any more data.
        const SEND = 1 << 1;
    }
}

impl From<StreamShutdown> for U32<LittleEndian> {
    fn from(flags: StreamShutdown) -> Self {
        flags.bits().into()
    }
}
