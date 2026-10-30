//! Driver for VirtIO random number generator devices.
use super::common::Feature;
use crate::{queue::VirtQueue, transport::Transport, Hal, Result};

// VirtioRNG only uses one queue
const QUEUE_IDX: u16 = 0;
const QUEUE_SIZE: usize = 8;
const SUPPORTED_FEATURES: Feature = Feature::RING_INDIRECT_DESC.union(Feature::RING_EVENT_IDX);

/// Driver for a VirtIO random number generator device.
pub struct VirtIORng<H: Hal, T: Transport> {
    transport: T,
    queue: VirtQueue<H, QUEUE_SIZE>,
}

impl<H: Hal, T: Transport> VirtIORng<H, T> {
    /// Create a new driver with the given transport.
    pub fn new(mut transport: T) -> Result<Self> {
        let feat = transport.begin_init(SUPPORTED_FEATURES);
        let queue = VirtQueue::new(
            &mut transport,
            QUEUE_IDX,
            feat.contains(Feature::RING_INDIRECT_DESC),
            feat.contains(Feature::RING_EVENT_IDX),
        )?;
        transport.finish_init();
        Ok(Self { transport, queue })
    }

    /// Request random bytes from the device to be stored into `dst`.
    pub fn request_entropy(&mut self, dst: &mut [u8]) -> Result<usize> {
        let num = self
            .queue
            .add_notify_wait_pop(&[], &mut [dst], &mut self.transport)?;
        Ok(num as usize)
    }

    /// Enable interrupts.
    pub fn enable_interrupts(&mut self) {
        self.queue.set_dev_notify(true);
    }

    /// Disable interrupts.
    pub fn disable_interrupts(&mut self) {
        self.queue.set_dev_notify(false);
    }

    /// Acknowledge interrupt.
    pub fn ack_interrupt(&mut self) -> bool {
        self.transport.ack_interrupt()
    }
}

impl<H: Hal, T: Transport> Drop for VirtIORng<H, T> {
    fn drop(&mut self) {
        self.transport.queue_unset(QUEUE_IDX);
    }
}
