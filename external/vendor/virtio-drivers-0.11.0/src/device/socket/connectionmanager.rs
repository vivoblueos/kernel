use super::{
    protocol::VsockAddr, vsock::ConnectionInfo, DisconnectReason, SocketError, VirtIOSocket,
    VsockEvent, VsockEventType, DEFAULT_RX_BUFFER_SIZE,
};
use crate::{transport::Transport, Hal, Result};
use alloc::{boxed::Box, vec::Vec};
use core::cmp::min;
use core::convert::TryInto;
use core::hint::spin_loop;
use log::debug;
use zerocopy::FromZeros;

const DEFAULT_PER_CONNECTION_BUFFER_CAPACITY: u32 = 1024;

/// A higher level interface for VirtIO socket (vsock) devices.
///
/// This keeps track of multiple vsock connections.
///
/// `RX_BUFFER_SIZE` is the size in bytes of each buffer used in the RX virtqueue. This must be
/// bigger than `size_of::<VirtioVsockHdr>()`.
///
/// # Example
///
/// ```
/// # use virtio_drivers::{Error, Hal};
/// # use virtio_drivers::transport::Transport;
/// use virtio_drivers::device::socket::{VirtIOSocket, VsockAddr, VsockConnectionManager};
///
/// # fn example<HalImpl: Hal, T: Transport>(transport: T) -> Result<(), Error> {
/// let mut socket = VsockConnectionManager::new(VirtIOSocket::<HalImpl, _>::new(transport)?);
///
/// // Start a thread to call `socket.poll()` and handle events.
///
/// let remote_address = VsockAddr { cid: 2, port: 42 };
/// let local_port = 1234;
/// socket.connect(remote_address, local_port)?;
///
/// // Wait until `socket.poll()` returns an event indicating that the socket is connected.
///
/// socket.send(remote_address, local_port, "Hello world".as_bytes())?;
///
/// socket.shutdown(remote_address, local_port)?;
/// # Ok(())
/// # }
/// ```
pub struct VsockConnectionManager<
    H: Hal,
    T: Transport,
    const RX_BUFFER_SIZE: usize = DEFAULT_RX_BUFFER_SIZE,
> {
    driver: VirtIOSocket<H, T, RX_BUFFER_SIZE>,
    per_connection_buffer_capacity: u32,
    connections: Vec<Connection>,
    listening_ports: Vec<u32>,
}

#[derive(Debug)]
struct Connection {
    info: ConnectionInfo,
    buffer: RingBuffer,
    /// The peer sent a SHUTDOWN request, but we haven't yet responded with a RST because there is
    /// still data in the buffer.
    peer_requested_shutdown: bool,
}

impl Connection {
    fn new(peer: VsockAddr, local_port: u32, buffer_capacity: u32) -> Self {
        let mut info = ConnectionInfo::new(peer, local_port);
        info.buf_alloc = buffer_capacity;
        Self {
            info,
            buffer: RingBuffer::new(buffer_capacity.try_into().unwrap()),
            peer_requested_shutdown: false,
        }
    }
}

impl<H: Hal, T: Transport, const RX_BUFFER_SIZE: usize>
    VsockConnectionManager<H, T, RX_BUFFER_SIZE>
{
    /// Construct a new connection manager wrapping the given low-level VirtIO socket driver.
    pub fn new(driver: VirtIOSocket<H, T, RX_BUFFER_SIZE>) -> Self {
        Self::new_with_capacity(driver, DEFAULT_PER_CONNECTION_BUFFER_CAPACITY)
    }

    /// Construct a new connection manager wrapping the given low-level VirtIO socket driver, with
    /// the given per-connection buffer capacity.
    pub fn new_with_capacity(
        driver: VirtIOSocket<H, T, RX_BUFFER_SIZE>,
        per_connection_buffer_capacity: u32,
    ) -> Self {
        Self {
            driver,
            connections: Vec::new(),
            listening_ports: Vec::new(),
            per_connection_buffer_capacity,
        }
    }

    /// Returns the CID which has been assigned to this guest.
    pub fn guest_cid(&self) -> u64 {
        self.driver.guest_cid()
    }

    /// Allows incoming connections on the given port number.
    pub fn listen(&mut self, port: u32) {
        if !self.listening_ports.contains(&port) {
            self.listening_ports.push(port);
        }
    }

    /// Stops allowing incoming connections on the given port number.
    pub fn unlisten(&mut self, port: u32) {
        self.listening_ports.retain(|p| *p != port);
    }

    /// Sends a request to connect to the given destination.
    ///
    /// This returns as soon as the request is sent; you should wait until `poll` returns a
    /// `VsockEventType::Connected` event indicating that the peer has accepted the connection
    /// before sending data.
    pub fn connect(&mut self, destination: VsockAddr, src_port: u32) -> Result {
        if self.connections.iter().any(|connection| {
            connection.info.dst == destination && connection.info.src_port == src_port
        }) {
            return Err(SocketError::ConnectionExists.into());
        }

        let new_connection =
            Connection::new(destination, src_port, self.per_connection_buffer_capacity);

        self.driver.connect(&new_connection.info)?;
        debug!("Connection requested: {:?}", new_connection.info);
        self.connections.push(new_connection);
        Ok(())
    }

    /// Sends the buffer to the destination.
    pub fn send(&mut self, destination: VsockAddr, src_port: u32, buffer: &[u8]) -> Result {
        let (_, connection) = get_connection(&mut self.connections, destination, src_port)?;

        self.driver.send(buffer, &mut connection.info)
    }

    /// Polls the vsock device to receive data or other updates.
    pub fn poll(&mut self) -> Result<Option<VsockEvent>> {
        let guest_cid = self.driver.guest_cid();
        let connections = &mut self.connections;
        let per_connection_buffer_capacity = self.per_connection_buffer_capacity;

        let result = self.driver.poll(|event, body| {
            let connection = get_connection_for_event(connections, &event, guest_cid);

            // Skip events which don't match any connection we know about, unless they are a
            // connection request.
            let connection = if let Some((_, connection)) = connection {
                connection
            } else if let VsockEventType::ConnectionRequest = event.event_type {
                // If the requested connection already exists or the CID isn't ours, ignore it.
                if connection.is_some() || event.destination.cid != guest_cid {
                    return Ok(None);
                }
                // Add the new connection to our list, at least for now. It will be removed again
                // below if we weren't listening on the port.
                connections.push(Connection::new(
                    event.source,
                    event.destination.port,
                    per_connection_buffer_capacity,
                ));
                connections.last_mut().unwrap()
            } else {
                return Ok(None);
            };

            // Update stored connection info.
            connection.info.update_for_event(&event);

            if let VsockEventType::Received { length } = event.event_type {
                // Copy to buffer
                if !connection.buffer.add(body) {
                    return Err(SocketError::OutputBufferTooShort(length).into());
                }
            }

            Ok(Some(event))
        })?;

        let Some(event) = result else {
            return Ok(None);
        };

        // The connection must exist because we found it above in the callback.
        let (connection_index, connection) =
            get_connection_for_event(connections, &event, guest_cid).unwrap();

        match event.event_type {
            VsockEventType::ConnectionRequest => {
                if self.listening_ports.contains(&event.destination.port) {
                    self.driver.accept(&connection.info)?;
                } else {
                    // Reject the connection request and remove it from our list.
                    self.driver.force_close(&connection.info)?;
                    self.connections.swap_remove(connection_index);

                    // No need to pass the request on to the client, as we've already rejected it.
                    return Ok(None);
                }
            }
            VsockEventType::Connected => {}
            VsockEventType::Disconnected { reason } => {
                // Wait until client reads all data before removing connection.
                if connection.buffer.is_empty() {
                    if reason == DisconnectReason::Shutdown {
                        self.driver.force_close(&connection.info)?;
                    }
                    self.connections.swap_remove(connection_index);
                } else {
                    connection.peer_requested_shutdown = true;
                }
            }
            VsockEventType::Received { .. } => {
                // Already copied the buffer in the callback above.
            }
            VsockEventType::CreditRequest => {
                // If the peer requested credit, send an update.
                self.driver.credit_update(&connection.info)?;
                // No need to pass the request on to the client, we've already handled it.
                return Ok(None);
            }
            VsockEventType::CreditUpdate => {}
        }

        Ok(Some(event))
    }

    /// Reads data received from the given connection.
    pub fn recv(&mut self, peer: VsockAddr, src_port: u32, buffer: &mut [u8]) -> Result<usize> {
        let (connection_index, connection) = get_connection(&mut self.connections, peer, src_port)?;

        // Copy from ring buffer
        let bytes_read = connection.buffer.drain(buffer);

        connection.info.done_forwarding(bytes_read);

        // If buffer is now empty and the peer requested shutdown, finish shutting down the
        // connection.
        if connection.peer_requested_shutdown && connection.buffer.is_empty() {
            self.driver.force_close(&connection.info)?;
            self.connections.swap_remove(connection_index);
        }

        Ok(bytes_read)
    }

    /// Returns the number of bytes in the receive buffer available to be read by `recv`.
    ///
    /// When the available bytes is 0, it indicates that the receive buffer is empty and does not
    /// contain any data.
    pub fn recv_buffer_available_bytes(&mut self, peer: VsockAddr, src_port: u32) -> Result<usize> {
        let (_, connection) = get_connection(&mut self.connections, peer, src_port)?;
        Ok(connection.buffer.used())
    }

    /// Sends a credit update to the given peer.
    pub fn update_credit(&mut self, peer: VsockAddr, src_port: u32) -> Result {
        let (_, connection) = get_connection(&mut self.connections, peer, src_port)?;
        self.driver.credit_update(&connection.info)
    }

    /// Blocks until we get some event from the vsock device.
    pub fn wait_for_event(&mut self) -> Result<VsockEvent> {
        loop {
            if let Some(event) = self.poll()? {
                return Ok(event);
            } else {
                spin_loop();
            }
        }
    }

    /// Requests to shut down the connection cleanly, telling the peer that we won't send or receive
    /// any more data.
    ///
    /// This returns as soon as the request is sent; you should wait until `poll` returns a
    /// `VsockEventType::Disconnected` event if you want to know that the peer has acknowledged the
    /// shutdown.
    pub fn shutdown(&mut self, destination: VsockAddr, src_port: u32) -> Result {
        let (_, connection) = get_connection(&mut self.connections, destination, src_port)?;

        self.driver.shutdown(&connection.info)
    }

    /// Forcibly closes the connection without waiting for the peer.
    pub fn force_close(&mut self, destination: VsockAddr, src_port: u32) -> Result {
        let (index, connection) = get_connection(&mut self.connections, destination, src_port)?;

        self.driver.force_close(&connection.info)?;

        self.connections.swap_remove(index);
        Ok(())
    }
}

/// Returns the connection from the given list matching the given peer address and local port, and
/// its index.
///
/// Returns `Err(SocketError::NotConnected)` if there is no matching connection in the list.
fn get_connection(
    connections: &mut [Connection],
    peer: VsockAddr,
    local_port: u32,
) -> core::result::Result<(usize, &mut Connection), SocketError> {
    connections
        .iter_mut()
        .enumerate()
        .find(|(_, connection)| {
            connection.info.dst == peer && connection.info.src_port == local_port
        })
        .ok_or(SocketError::NotConnected)
}

/// Returns the connection from the given list matching the event, if any, and its index.
fn get_connection_for_event<'a>(
    connections: &'a mut [Connection],
    event: &VsockEvent,
    local_cid: u64,
) -> Option<(usize, &'a mut Connection)> {
    connections
        .iter_mut()
        .enumerate()
        .find(|(_, connection)| event.matches_connection(&connection.info, local_cid))
}

#[derive(Debug)]
struct RingBuffer {
    buffer: Box<[u8]>,
    /// The number of bytes currently in the buffer.
    used: usize,
    /// The index of the first used byte in the buffer.
    start: usize,
}

impl RingBuffer {
    pub fn new(capacity: usize) -> Self {
        Self {
            buffer: FromZeros::new_box_zeroed_with_elems(capacity).unwrap(),
            used: 0,
            start: 0,
        }
    }

    /// Returns the number of bytes currently used in the buffer.
    pub fn used(&self) -> usize {
        self.used
    }

    /// Returns true iff there are currently no bytes in the buffer.
    pub fn is_empty(&self) -> bool {
        self.used == 0
    }

    /// Returns the number of bytes currently free in the buffer.
    pub fn free(&self) -> usize {
        self.buffer.len() - self.used
    }

    /// Adds the given bytes to the buffer if there is enough capacity for them all.
    ///
    /// Returns true if they were added, or false if they were not.
    pub fn add(&mut self, bytes: &[u8]) -> bool {
        if bytes.len() > self.free() {
            return false;
        }

        // The index of the first available position in the buffer.
        let first_available = (self.start + self.used) % self.buffer.len();
        // The number of bytes to copy from `bytes` to `buffer` between `first_available` and
        // `buffer.len()`.
        let copy_length_before_wraparound = min(bytes.len(), self.buffer.len() - first_available);
        self.buffer[first_available..first_available + copy_length_before_wraparound]
            .copy_from_slice(&bytes[0..copy_length_before_wraparound]);
        if let Some(bytes_after_wraparound) = bytes.get(copy_length_before_wraparound..) {
            self.buffer[0..bytes_after_wraparound.len()].copy_from_slice(bytes_after_wraparound);
        }
        self.used += bytes.len();

        true
    }

    /// Reads and removes as many bytes as possible from the buffer, up to the length of the given
    /// buffer.
    pub fn drain(&mut self, out: &mut [u8]) -> usize {
        let bytes_read = min(self.used, out.len());

        // The number of bytes to copy out between `start` and the end of the buffer.
        let read_before_wraparound = min(bytes_read, self.buffer.len() - self.start);
        // The number of bytes to copy out from the beginning of the buffer after wrapping around.
        let read_after_wraparound = bytes_read
            .checked_sub(read_before_wraparound)
            .unwrap_or_default();

        out[0..read_before_wraparound]
            .copy_from_slice(&self.buffer[self.start..self.start + read_before_wraparound]);
        out[read_before_wraparound..bytes_read]
            .copy_from_slice(&self.buffer[0..read_after_wraparound]);

        self.used -= bytes_read;
        self.start = (self.start + bytes_read) % self.buffer.len();

        bytes_read
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        config::ReadOnly,
        device::socket::{
            protocol::{
                SocketType, StreamShutdown, VirtioVsockConfig, VirtioVsockHdr, VirtioVsockOp,
            },
            vsock::{VsockBufferStatus, QUEUE_SIZE, RX_QUEUE_IDX, TX_QUEUE_IDX},
        },
        hal::fake::FakeHal,
        transport::{
            fake::{FakeTransport, QueueStatus, State},
            DeviceType,
        },
    };
    use alloc::{sync::Arc, vec};
    use core::mem::size_of;
    use std::{sync::Mutex, thread};
    use zerocopy::{FromBytes, IntoBytes};

    #[test]
    fn send_recv() {
        let host_cid = 2;
        let guest_cid = 66;
        let host_port = 1234;
        let guest_port = 4321;
        let host_address = VsockAddr {
            cid: host_cid,
            port: host_port,
        };
        let hello_from_guest = "Hello from guest";
        let hello_from_host = "Hello from host";

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
        let mut socket = VsockConnectionManager::new(
            VirtIOSocket::<FakeHal, FakeTransport<VirtioVsockConfig>>::new(transport).unwrap(),
        );

        // Start a thread to simulate the device.
        let handle = thread::spawn(move || {
            // Wait for connection request.
            State::wait_until_queue_notified(&state, TX_QUEUE_IDX);
            assert_eq!(
                VirtioVsockHdr::read_from_bytes(
                    state
                        .lock()
                        .unwrap()
                        .read_from_queue::<QUEUE_SIZE>(TX_QUEUE_IDX)
                        .as_slice()
                )
                .unwrap(),
                VirtioVsockHdr {
                    op: VirtioVsockOp::Request.into(),
                    src_cid: guest_cid.into(),
                    dst_cid: host_cid.into(),
                    src_port: guest_port.into(),
                    dst_port: host_port.into(),
                    len: 0.into(),
                    socket_type: SocketType::Stream.into(),
                    flags: 0.into(),
                    buf_alloc: 1024.into(),
                    fwd_cnt: 0.into(),
                }
            );

            // Accept connection and give the peer enough credit to send the message.
            state.lock().unwrap().write_to_queue::<QUEUE_SIZE>(
                RX_QUEUE_IDX,
                VirtioVsockHdr {
                    op: VirtioVsockOp::Response.into(),
                    src_cid: host_cid.into(),
                    dst_cid: guest_cid.into(),
                    src_port: host_port.into(),
                    dst_port: guest_port.into(),
                    len: 0.into(),
                    socket_type: SocketType::Stream.into(),
                    flags: 0.into(),
                    buf_alloc: 50.into(),
                    fwd_cnt: 0.into(),
                }
                .as_bytes(),
            );

            // Expect the guest to send some data.
            State::wait_until_queue_notified(&state, TX_QUEUE_IDX);
            let request = state
                .lock()
                .unwrap()
                .read_from_queue::<QUEUE_SIZE>(TX_QUEUE_IDX);
            assert_eq!(
                request.len(),
                size_of::<VirtioVsockHdr>() + hello_from_guest.len()
            );
            assert_eq!(
                VirtioVsockHdr::read_from_prefix(request.as_slice())
                    .unwrap()
                    .0,
                VirtioVsockHdr {
                    op: VirtioVsockOp::Rw.into(),
                    src_cid: guest_cid.into(),
                    dst_cid: host_cid.into(),
                    src_port: guest_port.into(),
                    dst_port: host_port.into(),
                    len: (hello_from_guest.len() as u32).into(),
                    socket_type: SocketType::Stream.into(),
                    flags: 0.into(),
                    buf_alloc: 1024.into(),
                    fwd_cnt: 0.into(),
                }
            );
            assert_eq!(
                &request[size_of::<VirtioVsockHdr>()..],
                hello_from_guest.as_bytes()
            );

            println!("Host sending");

            // Send a response.
            let mut response = vec![0; size_of::<VirtioVsockHdr>() + hello_from_host.len()];
            VirtioVsockHdr {
                op: VirtioVsockOp::Rw.into(),
                src_cid: host_cid.into(),
                dst_cid: guest_cid.into(),
                src_port: host_port.into(),
                dst_port: guest_port.into(),
                len: (hello_from_host.len() as u32).into(),
                socket_type: SocketType::Stream.into(),
                flags: 0.into(),
                buf_alloc: 50.into(),
                fwd_cnt: (hello_from_guest.len() as u32).into(),
            }
            .write_to_prefix(response.as_mut_slice())
            .unwrap();
            response[size_of::<VirtioVsockHdr>()..].copy_from_slice(hello_from_host.as_bytes());
            state
                .lock()
                .unwrap()
                .write_to_queue::<QUEUE_SIZE>(RX_QUEUE_IDX, &response);

            // Expect a shutdown.
            State::wait_until_queue_notified(&state, TX_QUEUE_IDX);
            assert_eq!(
                VirtioVsockHdr::read_from_bytes(
                    state
                        .lock()
                        .unwrap()
                        .read_from_queue::<QUEUE_SIZE>(TX_QUEUE_IDX)
                        .as_slice()
                )
                .unwrap(),
                VirtioVsockHdr {
                    op: VirtioVsockOp::Shutdown.into(),
                    src_cid: guest_cid.into(),
                    dst_cid: host_cid.into(),
                    src_port: guest_port.into(),
                    dst_port: host_port.into(),
                    len: 0.into(),
                    socket_type: SocketType::Stream.into(),
                    flags: (StreamShutdown::SEND | StreamShutdown::RECEIVE).into(),
                    buf_alloc: 1024.into(),
                    fwd_cnt: (hello_from_host.len() as u32).into(),
                }
            );
        });

        socket.connect(host_address, guest_port).unwrap();
        assert_eq!(
            socket.wait_for_event().unwrap(),
            VsockEvent {
                source: host_address,
                destination: VsockAddr {
                    cid: guest_cid,
                    port: guest_port,
                },
                event_type: VsockEventType::Connected,
                buffer_status: VsockBufferStatus {
                    buffer_allocation: 50,
                    forward_count: 0,
                },
            }
        );
        println!("Guest sending");
        socket
            .send(host_address, guest_port, "Hello from guest".as_bytes())
            .unwrap();
        println!("Guest waiting to receive.");
        assert_eq!(
            socket.wait_for_event().unwrap(),
            VsockEvent {
                source: host_address,
                destination: VsockAddr {
                    cid: guest_cid,
                    port: guest_port,
                },
                event_type: VsockEventType::Received {
                    length: hello_from_host.len()
                },
                buffer_status: VsockBufferStatus {
                    buffer_allocation: 50,
                    forward_count: hello_from_guest.len() as u32,
                },
            }
        );
        println!("Guest getting received data.");
        let mut buffer = [0u8; 64];
        assert_eq!(
            socket.recv(host_address, guest_port, &mut buffer).unwrap(),
            hello_from_host.len()
        );
        assert_eq!(
            &buffer[0..hello_from_host.len()],
            hello_from_host.as_bytes()
        );
        socket.shutdown(host_address, guest_port).unwrap();

        handle.join().unwrap();
    }

    #[test]
    fn incoming_connection() {
        let host_cid = 2;
        let guest_cid = 66;
        let host_port = 1234;
        let guest_port = 4321;
        let wrong_guest_port = 4444;
        let host_address = VsockAddr {
            cid: host_cid,
            port: host_port,
        };

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
        let mut socket = VsockConnectionManager::new(
            VirtIOSocket::<FakeHal, FakeTransport<VirtioVsockConfig>>::new(transport).unwrap(),
        );

        socket.listen(guest_port);

        // Start a thread to simulate the device.
        let handle = thread::spawn(move || {
            // Send a connection request for a port the guest isn't listening on.
            println!("Host sending connection request to wrong port");
            state.lock().unwrap().write_to_queue::<QUEUE_SIZE>(
                RX_QUEUE_IDX,
                VirtioVsockHdr {
                    op: VirtioVsockOp::Request.into(),
                    src_cid: host_cid.into(),
                    dst_cid: guest_cid.into(),
                    src_port: host_port.into(),
                    dst_port: wrong_guest_port.into(),
                    len: 0.into(),
                    socket_type: SocketType::Stream.into(),
                    flags: 0.into(),
                    buf_alloc: 50.into(),
                    fwd_cnt: 0.into(),
                }
                .as_bytes(),
            );

            // Expect a rejection.
            println!("Host waiting for rejection");
            State::wait_until_queue_notified(&state, TX_QUEUE_IDX);
            assert_eq!(
                VirtioVsockHdr::read_from_bytes(
                    state
                        .lock()
                        .unwrap()
                        .read_from_queue::<QUEUE_SIZE>(TX_QUEUE_IDX)
                        .as_slice()
                )
                .unwrap(),
                VirtioVsockHdr {
                    op: VirtioVsockOp::Rst.into(),
                    src_cid: guest_cid.into(),
                    dst_cid: host_cid.into(),
                    src_port: wrong_guest_port.into(),
                    dst_port: host_port.into(),
                    len: 0.into(),
                    socket_type: SocketType::Stream.into(),
                    flags: 0.into(),
                    buf_alloc: 1024.into(),
                    fwd_cnt: 0.into(),
                }
            );

            // Send a connection request for a port the guest is listening on.
            println!("Host sending connection request to right port");
            state.lock().unwrap().write_to_queue::<QUEUE_SIZE>(
                RX_QUEUE_IDX,
                VirtioVsockHdr {
                    op: VirtioVsockOp::Request.into(),
                    src_cid: host_cid.into(),
                    dst_cid: guest_cid.into(),
                    src_port: host_port.into(),
                    dst_port: guest_port.into(),
                    len: 0.into(),
                    socket_type: SocketType::Stream.into(),
                    flags: 0.into(),
                    buf_alloc: 50.into(),
                    fwd_cnt: 0.into(),
                }
                .as_bytes(),
            );

            // Expect a response.
            println!("Host waiting for response");
            State::wait_until_queue_notified(&state, TX_QUEUE_IDX);
            assert_eq!(
                VirtioVsockHdr::read_from_bytes(
                    state
                        .lock()
                        .unwrap()
                        .read_from_queue::<QUEUE_SIZE>(TX_QUEUE_IDX)
                        .as_slice()
                )
                .unwrap(),
                VirtioVsockHdr {
                    op: VirtioVsockOp::Response.into(),
                    src_cid: guest_cid.into(),
                    dst_cid: host_cid.into(),
                    src_port: guest_port.into(),
                    dst_port: host_port.into(),
                    len: 0.into(),
                    socket_type: SocketType::Stream.into(),
                    flags: 0.into(),
                    buf_alloc: 1024.into(),
                    fwd_cnt: 0.into(),
                }
            );

            println!("Host finished");
        });

        // Expect an incoming connection.
        println!("Guest expecting incoming connection.");
        assert_eq!(
            socket.wait_for_event().unwrap(),
            VsockEvent {
                source: host_address,
                destination: VsockAddr {
                    cid: guest_cid,
                    port: guest_port,
                },
                event_type: VsockEventType::ConnectionRequest,
                buffer_status: VsockBufferStatus {
                    buffer_allocation: 50,
                    forward_count: 0,
                },
            }
        );

        handle.join().unwrap();
    }
}
