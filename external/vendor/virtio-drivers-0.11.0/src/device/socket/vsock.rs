//! Driver for VirtIO socket devices.
#![deny(unsafe_op_in_unsafe_fn)]

use super::error::SocketError;
use super::protocol::{
    Feature, StreamShutdown, VirtioVsockConfig, VirtioVsockHdr, VirtioVsockOp, VsockAddr,
};
use super::DEFAULT_RX_BUFFER_SIZE;
use crate::config::read_config;
use crate::hal::Hal;
use crate::queue::{owning::OwningQueue, VirtQueue};
use crate::transport::Transport;
use crate::Result;
use core::mem::size_of;
use log::debug;
use zerocopy::{FromBytes, IntoBytes};

pub(crate) const RX_QUEUE_IDX: u16 = 0;
pub(crate) const TX_QUEUE_IDX: u16 = 1;
const EVENT_QUEUE_IDX: u16 = 2;

pub(crate) const QUEUE_SIZE: usize = 8;
const SUPPORTED_FEATURES: Feature = Feature::RING_EVENT_IDX.union(Feature::RING_INDIRECT_DESC);

/// Information about a particular vsock connection.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ConnectionInfo {
    /// The address of the peer.
    pub dst: VsockAddr,
    /// The local port number associated with the connection.
    pub src_port: u32,
    /// The last `buf_alloc` value the peer sent to us, indicating how much receive buffer space in
    /// bytes it has allocated for packet bodies.
    peer_buf_alloc: u32,
    /// The last `fwd_cnt` value the peer sent to us, indicating how many bytes of packet bodies it
    /// has finished processing.
    peer_fwd_cnt: u32,
    /// The number of bytes of packet bodies which we have sent to the peer.
    tx_cnt: u32,
    /// The number of bytes of buffer space we have allocated to receive packet bodies from the
    /// peer.
    pub buf_alloc: u32,
    /// The number of bytes of packet bodies which we have received from the peer and handled.
    fwd_cnt: u32,
    /// Whether we have recently requested credit from the peer.
    ///
    /// This is set to true when we send a `VIRTIO_VSOCK_OP_CREDIT_REQUEST`, and false when we
    /// receive a `VIRTIO_VSOCK_OP_CREDIT_UPDATE`.
    has_pending_credit_request: bool,
}

impl ConnectionInfo {
    /// Creates a new `ConnectionInfo` for the given peer address and local port, and default values
    /// for everything else.
    pub fn new(destination: VsockAddr, src_port: u32) -> Self {
        Self {
            dst: destination,
            src_port,
            ..Default::default()
        }
    }

    /// Updates this connection info with the peer buffer allocation and forwarded count from the
    /// given event.
    pub fn update_for_event(&mut self, event: &VsockEvent) {
        self.peer_buf_alloc = event.buffer_status.buffer_allocation;
        self.peer_fwd_cnt = event.buffer_status.forward_count;

        if let VsockEventType::CreditUpdate = event.event_type {
            self.has_pending_credit_request = false;
        }
    }

    /// Increases the forwarded count recorded for this connection by the given number of bytes.
    ///
    /// This should be called once received data has been passed to the client, so there is buffer
    /// space available for more.
    pub fn done_forwarding(&mut self, length: usize) {
        self.fwd_cnt += length as u32;
    }

    /// Returns the number of bytes of RX buffer space the peer has available to receive packet body
    /// data from us.
    fn peer_free(&self) -> u32 {
        self.peer_buf_alloc - (self.tx_cnt - self.peer_fwd_cnt)
    }

    fn new_header(&self, src_cid: u64) -> VirtioVsockHdr {
        VirtioVsockHdr {
            src_cid: src_cid.into(),
            dst_cid: self.dst.cid.into(),
            src_port: self.src_port.into(),
            dst_port: self.dst.port.into(),
            buf_alloc: self.buf_alloc.into(),
            fwd_cnt: self.fwd_cnt.into(),
            ..Default::default()
        }
    }
}

/// An event received from a VirtIO socket device.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VsockEvent {
    /// The source of the event, i.e. the peer who sent it.
    pub source: VsockAddr,
    /// The destination of the event, i.e. the CID and port on our side.
    pub destination: VsockAddr,
    /// The peer's buffer status for the connection.
    pub buffer_status: VsockBufferStatus,
    /// The type of event.
    pub event_type: VsockEventType,
}

impl VsockEvent {
    /// Returns whether the event matches the given connection.
    pub fn matches_connection(&self, connection_info: &ConnectionInfo, guest_cid: u64) -> bool {
        self.source == connection_info.dst
            && self.destination.cid == guest_cid
            && self.destination.port == connection_info.src_port
    }

    fn from_header(header: &VirtioVsockHdr) -> Result<Self> {
        let op = header.op()?;
        let buffer_status = VsockBufferStatus {
            buffer_allocation: header.buf_alloc.into(),
            forward_count: header.fwd_cnt.into(),
        };
        let source = header.source();
        let destination = header.destination();

        let event_type = match op {
            VirtioVsockOp::Request => {
                header.check_data_is_empty()?;
                VsockEventType::ConnectionRequest
            }
            VirtioVsockOp::Response => {
                header.check_data_is_empty()?;
                VsockEventType::Connected
            }
            VirtioVsockOp::CreditUpdate => {
                header.check_data_is_empty()?;
                VsockEventType::CreditUpdate
            }
            VirtioVsockOp::Rst | VirtioVsockOp::Shutdown => {
                header.check_data_is_empty()?;
                debug!("Disconnected from the peer");
                let reason = if op == VirtioVsockOp::Rst {
                    DisconnectReason::Reset
                } else {
                    DisconnectReason::Shutdown
                };
                VsockEventType::Disconnected { reason }
            }
            VirtioVsockOp::Rw => VsockEventType::Received {
                length: header.len() as usize,
            },
            VirtioVsockOp::CreditRequest => {
                header.check_data_is_empty()?;
                VsockEventType::CreditRequest
            }
            VirtioVsockOp::Invalid => return Err(SocketError::InvalidOperation.into()),
        };

        Ok(VsockEvent {
            source,
            destination,
            buffer_status,
            event_type,
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VsockBufferStatus {
    pub buffer_allocation: u32,
    pub forward_count: u32,
}

/// The reason why a vsock connection was closed.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum DisconnectReason {
    /// The peer has either closed the connection in response to our shutdown request, or forcibly
    /// closed it of its own accord.
    Reset,
    /// The peer asked to shut down the connection.
    Shutdown,
}

/// Details of the type of an event received from a VirtIO socket.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum VsockEventType {
    /// The peer requests to establish a connection with us.
    ConnectionRequest,
    /// The connection was successfully established.
    Connected,
    /// The connection was closed.
    Disconnected {
        /// The reason for the disconnection.
        reason: DisconnectReason,
    },
    /// Data was received on the connection.
    Received {
        /// The length of the data in bytes.
        length: usize,
    },
    /// The peer requests us to send a credit update.
    CreditRequest,
    /// The peer just sent us a credit update with nothing else.
    CreditUpdate,
}

/// Low-level driver for a VirtIO socket device.
///
/// You probably want to use [`VsockConnectionManager`](super::VsockConnectionManager) rather than
/// using this directly.
///
/// `RX_BUFFER_SIZE` is the size in bytes of each buffer used in the RX virtqueue. This must be
/// bigger than `size_of::<VirtioVsockHdr>()`.
pub struct VirtIOSocket<H: Hal, T: Transport, const RX_BUFFER_SIZE: usize = DEFAULT_RX_BUFFER_SIZE>
{
    transport: T,
    /// Virtqueue to receive packets.
    rx: OwningQueue<H, QUEUE_SIZE, RX_BUFFER_SIZE>,
    tx: VirtQueue<H, { QUEUE_SIZE }>,
    /// Virtqueue to receive events from the device.
    event: VirtQueue<H, { QUEUE_SIZE }>,
    /// The guest_cid field contains the guest’s context ID, which uniquely identifies
    /// the device for its lifetime. The upper 32 bits of the CID are reserved and zeroed.
    guest_cid: u64,
}

impl<H: Hal, T: Transport, const RX_BUFFER_SIZE: usize> Drop
    for VirtIOSocket<H, T, RX_BUFFER_SIZE>
{
    fn drop(&mut self) {
        // Clear any pointers pointing to DMA regions, so the device doesn't try to access them
        // after they have been freed.
        self.transport.queue_unset(RX_QUEUE_IDX);
        self.transport.queue_unset(TX_QUEUE_IDX);
        self.transport.queue_unset(EVENT_QUEUE_IDX);
    }
}

impl<H: Hal, T: Transport, const RX_BUFFER_SIZE: usize> VirtIOSocket<H, T, RX_BUFFER_SIZE> {
    /// Create a new VirtIO Vsock driver.
    pub fn new(mut transport: T) -> Result<Self> {
        assert!(RX_BUFFER_SIZE > size_of::<VirtioVsockHdr>());

        let negotiated_features = transport.begin_init(SUPPORTED_FEATURES);

        let guest_cid = transport.read_consistent(|| {
            Ok(
                (read_config!(transport, VirtioVsockConfig, guest_cid_low)? as u64)
                    | ((read_config!(transport, VirtioVsockConfig, guest_cid_high)? as u64) << 32),
            )
        })?;
        debug!("guest cid: {guest_cid:?}");

        let rx = VirtQueue::new(
            &mut transport,
            RX_QUEUE_IDX,
            negotiated_features.contains(Feature::RING_INDIRECT_DESC),
            negotiated_features.contains(Feature::RING_EVENT_IDX),
        )?;
        let tx = VirtQueue::new(
            &mut transport,
            TX_QUEUE_IDX,
            negotiated_features.contains(Feature::RING_INDIRECT_DESC),
            negotiated_features.contains(Feature::RING_EVENT_IDX),
        )?;
        let event = VirtQueue::new(
            &mut transport,
            EVENT_QUEUE_IDX,
            negotiated_features.contains(Feature::RING_INDIRECT_DESC),
            negotiated_features.contains(Feature::RING_EVENT_IDX),
        )?;

        let rx = OwningQueue::new(rx)?;

        transport.finish_init();
        if rx.should_notify() {
            transport.notify(RX_QUEUE_IDX);
        }

        Ok(Self {
            transport,
            rx,
            tx,
            event,
            guest_cid,
        })
    }

    /// Returns the CID which has been assigned to this guest.
    pub fn guest_cid(&self) -> u64 {
        self.guest_cid
    }

    /// Sends a request to connect to the given destination.
    ///
    /// This returns as soon as the request is sent; you should wait until `poll` returns a
    /// `VsockEventType::Connected` event indicating that the peer has accepted the connection
    /// before sending data.
    pub fn connect(&mut self, connection_info: &ConnectionInfo) -> Result {
        let header = VirtioVsockHdr {
            op: VirtioVsockOp::Request.into(),
            ..connection_info.new_header(self.guest_cid)
        };
        // Sends a header only packet to the TX queue to connect the device to the listening socket
        // at the given destination.
        self.send_packet_to_tx_queue(&header, &[])
    }

    /// Accepts the given connection from a peer.
    pub fn accept(&mut self, connection_info: &ConnectionInfo) -> Result {
        let header = VirtioVsockHdr {
            op: VirtioVsockOp::Response.into(),
            ..connection_info.new_header(self.guest_cid)
        };
        self.send_packet_to_tx_queue(&header, &[])
    }

    /// Requests the peer to send us a credit update for the given connection.
    fn request_credit(&mut self, connection_info: &ConnectionInfo) -> Result {
        let header = VirtioVsockHdr {
            op: VirtioVsockOp::CreditRequest.into(),
            ..connection_info.new_header(self.guest_cid)
        };
        self.send_packet_to_tx_queue(&header, &[])
    }

    /// Sends the buffer to the destination.
    pub fn send(&mut self, buffer: &[u8], connection_info: &mut ConnectionInfo) -> Result {
        self.check_peer_buffer_is_sufficient(connection_info, buffer.len())?;

        let len = buffer.len() as u32;
        let header = VirtioVsockHdr {
            op: VirtioVsockOp::Rw.into(),
            len: len.into(),
            ..connection_info.new_header(self.guest_cid)
        };
        connection_info.tx_cnt += len;
        self.send_packet_to_tx_queue(&header, buffer)
    }

    fn check_peer_buffer_is_sufficient(
        &mut self,
        connection_info: &mut ConnectionInfo,
        buffer_len: usize,
    ) -> Result {
        if connection_info.peer_free() as usize >= buffer_len {
            Ok(())
        } else {
            // Request an update of the cached peer credit, if we haven't already done so, and tell
            // the caller to try again later.
            if !connection_info.has_pending_credit_request {
                self.request_credit(connection_info)?;
                connection_info.has_pending_credit_request = true;
            }
            Err(SocketError::InsufficientBufferSpaceInPeer.into())
        }
    }

    /// Tells the peer how much buffer space we have to receive data.
    pub fn credit_update(&mut self, connection_info: &ConnectionInfo) -> Result {
        let header = VirtioVsockHdr {
            op: VirtioVsockOp::CreditUpdate.into(),
            ..connection_info.new_header(self.guest_cid)
        };
        self.send_packet_to_tx_queue(&header, &[])
    }

    /// Polls the RX virtqueue for the next event, and calls the given handler function to handle
    /// it.
    pub fn poll(
        &mut self,
        handler: impl FnOnce(VsockEvent, &[u8]) -> Result<Option<VsockEvent>>,
    ) -> Result<Option<VsockEvent>> {
        self.rx.poll(&mut self.transport, |buffer| {
            let (header, body) = read_header_and_body(buffer)?;
            VsockEvent::from_header(&header).and_then(|event| handler(event, body))
        })
    }

    /// Requests to shut down the connection cleanly, sending hints about whether we will send or
    /// receive more data.
    ///
    /// This returns as soon as the request is sent; you should wait until `poll` returns a
    /// `VsockEventType::Disconnected` event if you want to know that the peer has acknowledged the
    /// shutdown.
    pub fn shutdown_with_hints(
        &mut self,
        connection_info: &ConnectionInfo,
        hints: StreamShutdown,
    ) -> Result {
        let header = VirtioVsockHdr {
            op: VirtioVsockOp::Shutdown.into(),
            flags: hints.into(),
            ..connection_info.new_header(self.guest_cid)
        };
        self.send_packet_to_tx_queue(&header, &[])
    }

    /// Requests to shut down the connection cleanly, telling the peer that we won't send or receive
    /// any more data.
    ///
    /// This returns as soon as the request is sent; you should wait until `poll` returns a
    /// `VsockEventType::Disconnected` event if you want to know that the peer has acknowledged the
    /// shutdown.
    pub fn shutdown(&mut self, connection_info: &ConnectionInfo) -> Result {
        self.shutdown_with_hints(
            connection_info,
            StreamShutdown::SEND | StreamShutdown::RECEIVE,
        )
    }

    /// Forcibly closes the connection without waiting for the peer.
    pub fn force_close(&mut self, connection_info: &ConnectionInfo) -> Result {
        let header = VirtioVsockHdr {
            op: VirtioVsockOp::Rst.into(),
            ..connection_info.new_header(self.guest_cid)
        };
        self.send_packet_to_tx_queue(&header, &[])?;
        Ok(())
    }

    fn send_packet_to_tx_queue(&mut self, header: &VirtioVsockHdr, buffer: &[u8]) -> Result {
        let _len = if buffer.is_empty() {
            self.tx
                .add_notify_wait_pop(&[header.as_bytes()], &mut [], &mut self.transport)?
        } else {
            self.tx.add_notify_wait_pop(
                &[header.as_bytes(), buffer],
                &mut [],
                &mut self.transport,
            )?
        };
        Ok(())
    }
}

fn read_header_and_body(buffer: &[u8]) -> Result<(VirtioVsockHdr, &[u8])> {
    // This could fail if the device returns a buffer used length shorter than the header size.
    let header = VirtioVsockHdr::read_from_prefix(buffer)
        .map_err(|_| SocketError::BufferTooShort)?
        .0;
    let body_length = header.len() as usize;

    // This could fail if the device returns an unreasonably long body length.
    let data_end = size_of::<VirtioVsockHdr>()
        .checked_add(body_length)
        .ok_or(SocketError::InvalidNumber)?;
    // This could fail if the device returns a body length longer than buffer used length it
    // returned.
    let data = buffer
        .get(size_of::<VirtioVsockHdr>()..data_end)
        .ok_or(SocketError::BufferTooShort)?;
    Ok((header, data))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        config::ReadOnly,
        hal::fake::FakeHal,
        transport::{
            fake::{FakeTransport, QueueStatus, State},
            DeviceType,
        },
    };
    use alloc::{sync::Arc, vec};
    use std::sync::Mutex;

    #[test]
    fn config() {
        let config_space = VirtioVsockConfig {
            guest_cid_low: ReadOnly::new(66),
            guest_cid_high: ReadOnly::new(0),
        };
        let state = Arc::new(Mutex::new(State::new(
            vec![
                QueueStatus::default(),
                QueueStatus::default(),
                QueueStatus::default(),
            ],
            config_space,
        )));
        let transport = FakeTransport {
            device_type: DeviceType::Socket,
            max_queue_size: 32,
            device_features: 0,
            state: state.clone(),
        };
        let socket =
            VirtIOSocket::<FakeHal, FakeTransport<VirtioVsockConfig>>::new(transport).unwrap();
        assert_eq!(socket.guest_cid(), 0x00_0000_0042);
    }
}
