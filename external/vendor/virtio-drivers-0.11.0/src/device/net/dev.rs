use alloc::vec;

use super::net_buf::{RxBuffer, TxBuffer};
use super::{EthernetAddress, VirtIONetRaw};
use crate::{hal::Hal, transport::Transport, Error, Result};

/// Driver for a VirtIO network device.
///
/// Unlike [`VirtIONetRaw`], it uses [`RxBuffer`]s for transmission and
/// reception rather than the raw slices. On initialization, it pre-allocates
/// all receive buffers and puts them all in the receive queue.
///
/// The virtio network device is a virtual ethernet card.
///
/// It has enhanced rapidly and demonstrates clearly how support for new
/// features are added to an existing device.
/// Empty buffers are placed in one virtqueue for receiving packets, and
/// outgoing packets are enqueued into another for transmission in that order.
/// A third command queue is used to control advanced filtering features.
pub struct VirtIONet<H: Hal, T: Transport, const QUEUE_SIZE: usize> {
    inner: VirtIONetRaw<H, T, QUEUE_SIZE>,
    rx_buffers: [Option<RxBuffer>; QUEUE_SIZE],
}

impl<H: Hal, T: Transport, const QUEUE_SIZE: usize> VirtIONet<H, T, QUEUE_SIZE> {
    /// Create a new VirtIO-Net driver.
    pub fn new(transport: T, buf_len: usize) -> Result<Self> {
        let mut inner = VirtIONetRaw::new(transport)?;

        const NONE_BUF: Option<RxBuffer> = None;
        let mut rx_buffers = [NONE_BUF; QUEUE_SIZE];
        for (i, rx_buf_place) in rx_buffers.iter_mut().enumerate() {
            let mut rx_buf = RxBuffer::new(i, buf_len);
            // SAFETY: The buffer lives as long as the queue.
            let token = unsafe { inner.receive_begin(rx_buf.as_bytes_mut())? };
            assert_eq!(token, i as u16);
            *rx_buf_place = Some(rx_buf);
        }

        Ok(VirtIONet { inner, rx_buffers })
    }

    /// Acknowledge interrupt.
    pub fn ack_interrupt(&mut self) -> bool {
        self.inner.ack_interrupt()
    }

    /// Disable interrupts.
    pub fn disable_interrupts(&mut self) {
        self.inner.disable_interrupts()
    }

    /// Enable interrupts.
    pub fn enable_interrupts(&mut self) {
        self.inner.enable_interrupts()
    }

    /// Get MAC address.
    pub fn mac_address(&self) -> EthernetAddress {
        self.inner.mac_address()
    }

    /// Whether can send packet.
    pub fn can_send(&self) -> bool {
        self.inner.can_send()
    }

    /// Whether can receive packet.
    pub fn can_recv(&self) -> bool {
        self.inner.poll_receive().is_some()
    }

    /// Receives a [`RxBuffer`] from network. If currently no data, returns an
    /// error with type [`Error::NotReady`].
    ///
    /// It will try to pop a buffer that completed data reception in the
    /// NIC queue.
    pub fn receive(&mut self) -> Result<RxBuffer> {
        if let Some(token) = self.inner.poll_receive() {
            let mut rx_buf = self.rx_buffers[token as usize]
                .take()
                .ok_or(Error::WrongToken)?;
            if token != rx_buf.idx {
                return Err(Error::WrongToken);
            }

            // SAFETY: `token` == `rx_buf.idx`, so we are passing the same
            // buffer as we passed to `VirtQueue::add` and it is still valid.
            let (_hdr_len, pkt_len) =
                unsafe { self.inner.receive_complete(token, rx_buf.as_bytes_mut())? };
            rx_buf.set_packet_len(pkt_len);
            Ok(rx_buf)
        } else {
            Err(Error::NotReady)
        }
    }

    /// Gives back the ownership of `rx_buf`, and recycles it for next use.
    ///
    /// It will add the buffer back to the NIC queue.
    pub fn recycle_rx_buffer(&mut self, mut rx_buf: RxBuffer) -> Result {
        // SAFETY: We take the ownership of `rx_buf` back to `rx_buffers`,
        // so it lives as long as the queue.
        let new_token = unsafe { self.inner.receive_begin(rx_buf.as_bytes_mut()) }?;
        // `rx_buffers[new_token]` is expected to be `None` since it was taken
        // away at `Self::receive()` and has not been added back.
        if self.rx_buffers[new_token as usize].is_some() {
            return Err(Error::WrongToken);
        }
        rx_buf.idx = new_token;
        self.rx_buffers[new_token as usize] = Some(rx_buf);
        Ok(())
    }

    /// Allocate a new buffer for transmitting.
    pub fn new_tx_buffer(&self, buf_len: usize) -> TxBuffer {
        TxBuffer(vec![0; buf_len])
    }

    /// Sends a [`TxBuffer`] to the network, and blocks until the request
    /// completed.
    pub fn send(&mut self, tx_buf: TxBuffer) -> Result {
        self.inner.send(tx_buf.packet())
    }
}
