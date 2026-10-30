use super::VirtQueue;
use crate::{transport::Transport, Error, Hal, Result};
use alloc::boxed::Box;
use core::convert::TryInto;
use core::ptr::{null_mut, NonNull};
use zerocopy::FromZeros;

/// A wrapper around [`Queue`] that owns all the buffers that are passed to the queue.
#[derive(Debug)]
pub struct OwningQueue<H: Hal, const SIZE: usize, const BUFFER_SIZE: usize> {
    queue: VirtQueue<H, SIZE>,
    buffers: [NonNull<[u8; BUFFER_SIZE]>; SIZE],
}

impl<H: Hal, const SIZE: usize, const BUFFER_SIZE: usize> OwningQueue<H, SIZE, BUFFER_SIZE> {
    /// Constructs a new `OwningQueue` wrapping around the given `VirtQueue`.
    ///
    /// This will allocate `SIZE` buffers of `BUFFER_SIZE` bytes each and add them to the queue.
    ///
    /// The caller is responsible for notifying the device if `should_notify` returns true.
    pub fn new(mut queue: VirtQueue<H, SIZE>) -> Result<Self> {
        let mut buffers = [null_mut(); SIZE];
        for (i, queue_buffer) in buffers.iter_mut().enumerate() {
            let mut buffer: Box<[u8; BUFFER_SIZE]> = FromZeros::new_box_zeroed().unwrap();
            // SAFETY: The buffer lives as long as the queue, as specified in the function safety
            // requirement, and we don't access it until it is popped.
            let token = unsafe { queue.add(&[], &mut [buffer.as_mut_slice()]) }?;
            assert_eq!(i, token.into());
            *queue_buffer = Box::into_raw(buffer);
        }
        let buffers = buffers.map(|ptr| NonNull::new(ptr).unwrap());

        Ok(Self { queue, buffers })
    }

    /// Returns whether the driver should notify the device after adding a new buffer to the
    /// virtqueue.
    ///
    /// This will be false if the device has supressed notifications.
    pub fn should_notify(&self) -> bool {
        self.queue.should_notify()
    }

    /// Tells the device whether to send used buffer notifications.
    pub fn set_dev_notify(&mut self, enable: bool) {
        self.queue.set_dev_notify(enable);
    }

    /// Adds the buffer at the given index in `buffers` back to the queue.
    ///
    /// Automatically notifies the device if required.
    ///
    /// # Safety
    ///
    /// The buffer must not currently be in the RX queue, and no other references to it must exist
    /// between when this method is called and when it is popped from the queue.
    unsafe fn add_buffer_to_queue(&mut self, index: u16, transport: &mut impl Transport) -> Result {
        // SAFETY: The buffer lives as long as the queue, and the caller guarantees that it's not
        // currently in the queue or referred to anywhere else until it is popped.
        unsafe {
            let buffer = self
                .buffers
                .get_mut(usize::from(index))
                .ok_or(Error::WrongToken)?
                .as_mut();
            let new_token = self.queue.add(&[], &mut [buffer])?;
            // If the RX buffer somehow gets assigned a different token, then our safety assumptions
            // are broken and we can't safely continue to do anything with the device.
            assert_eq!(new_token, index);
        }

        if self.queue.should_notify() {
            transport.notify(self.queue.queue_idx);
        }

        Ok(())
    }

    fn pop(&mut self) -> Result<Option<(&[u8], u16)>> {
        let Some(token) = self.queue.peek_used() else {
            return Ok(None);
        };

        // SAFETY: The device has told us it has finished using the buffer, and there are no other
        // references to it.
        let buffer = unsafe { self.buffers[usize::from(token)].as_mut() };
        // SAFETY: We maintain a consistent mapping of tokens to buffers, so we pass the same buffer
        // to `pop_used` as we previously passed to `add` for the token. Once we add the buffer back
        // to the RX queue then we don't access it again until next time it is popped.
        let len = unsafe { self.queue.pop_used(token, &[], &mut [buffer])? }
            .try_into()
            .unwrap();

        Ok(Some((&buffer[0..len], token)))
    }

    /// Checks whether there are any buffers which the device has marked as used so the driver
    /// should now process. If so, passes the first one to the `handle` function and then adds it
    /// back to the queue.
    ///
    /// Returns an error if there is an error accessing the queue or `handler` returns an error.
    /// Returns `Ok(None)` if there are no pending buffers to handle, or if `handler` returns
    /// `Ok(None)`.
    ///
    /// If `handler` panics then the buffer will not be added back to the queue, so this should be
    /// avoided.
    pub fn poll<T>(
        &mut self,
        transport: &mut impl Transport,
        handler: impl FnOnce(&[u8]) -> Result<Option<T>>,
    ) -> Result<Option<T>> {
        let Some((buffer, token)) = self.pop()? else {
            return Ok(None);
        };

        let result = handler(buffer);

        // SAFETY: The buffer was just popped from the queue so it's not in it, and there won't be
        // any other references until next time it's popped.
        unsafe {
            self.add_buffer_to_queue(token, transport)?;
        }

        result
    }
}

// SAFETY: The `buffers` can be accessed from any thread.
unsafe impl<H: Hal, const SIZE: usize, const BUFFER_SIZE: usize> Send
    for OwningQueue<H, SIZE, BUFFER_SIZE>
where
    VirtQueue<H, SIZE>: Send,
{
}

// SAFETY: An `&OwningQueue` only allows calling `should_notify`.
unsafe impl<H: Hal, const SIZE: usize, const BUFFER_SIZE: usize> Sync
    for OwningQueue<H, SIZE, BUFFER_SIZE>
where
    VirtQueue<H, SIZE>: Sync,
{
}

impl<H: Hal, const SIZE: usize, const BUFFER_SIZE: usize> Drop
    for OwningQueue<H, SIZE, BUFFER_SIZE>
{
    fn drop(&mut self) {
        for buffer in self.buffers {
            // SAFETY: We obtained the buffer pointer from `Box::into_raw`, and it won't be used
            // anywhere else after the queue is destroyed.
            unsafe { drop(Box::from_raw(buffer.as_ptr())) };
        }
    }
}
