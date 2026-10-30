//! A fake implementation of `Transport` for unit tests.

use super::{DeviceStatus, DeviceType, Transport};
use crate::{
    queue::{fake_read_write_queue, Descriptor},
    Error, PhysAddr,
};
use alloc::{sync::Arc, vec::Vec};
use core::{
    fmt::{self, Debug, Formatter},
    sync::atomic::{AtomicBool, Ordering},
    time::Duration,
};
use std::{sync::Mutex, thread};
use zerocopy::{FromBytes, Immutable, IntoBytes};

/// A fake implementation of [`Transport`] for unit tests.
#[derive(Debug)]
pub struct FakeTransport<C> {
    /// The type of device which the transport should claim to be for.
    pub device_type: DeviceType,
    /// The maximum queue size supported by the transport.
    pub max_queue_size: u32,
    /// The device features which should be reported by the transport.
    pub device_features: u64,
    /// The mutable state of the transport.
    pub state: Arc<Mutex<State<C>>>,
}

impl<C: FromBytes + Immutable + IntoBytes> Transport for FakeTransport<C> {
    fn device_type(&self) -> DeviceType {
        self.device_type
    }

    fn read_device_features(&mut self) -> u64 {
        self.device_features
    }

    fn write_driver_features(&mut self, driver_features: u64) {
        self.state.lock().unwrap().driver_features = driver_features;
    }

    fn max_queue_size(&mut self, _queue: u16) -> u32 {
        self.max_queue_size
    }

    fn notify(&mut self, queue: u16) {
        self.state.lock().unwrap().queues[queue as usize]
            .notified
            .store(true, Ordering::SeqCst);
    }

    fn get_status(&self) -> DeviceStatus {
        self.state.lock().unwrap().status
    }

    fn set_status(&mut self, status: DeviceStatus) {
        self.state.lock().unwrap().status = status;
    }

    fn set_guest_page_size(&mut self, guest_page_size: u32) {
        self.state.lock().unwrap().guest_page_size = guest_page_size;
    }

    fn requires_legacy_layout(&self) -> bool {
        false
    }

    fn queue_set(
        &mut self,
        queue: u16,
        size: u32,
        descriptors: PhysAddr,
        driver_area: PhysAddr,
        device_area: PhysAddr,
    ) {
        let mut state = self.state.lock().unwrap();
        state.queues[queue as usize].size = size;
        state.queues[queue as usize].descriptors = descriptors;
        state.queues[queue as usize].driver_area = driver_area;
        state.queues[queue as usize].device_area = device_area;
    }

    fn queue_unset(&mut self, queue: u16) {
        let mut state = self.state.lock().unwrap();
        state.queues[queue as usize].size = 0;
        state.queues[queue as usize].descriptors = 0;
        state.queues[queue as usize].driver_area = 0;
        state.queues[queue as usize].device_area = 0;
    }

    fn queue_used(&mut self, queue: u16) -> bool {
        self.state.lock().unwrap().queues[queue as usize].descriptors != 0
    }

    fn ack_interrupt(&mut self) -> bool {
        let mut state = self.state.lock().unwrap();
        let pending = state.interrupt_pending;
        if pending {
            state.interrupt_pending = false;
        }
        pending
    }

    fn read_config_generation(&self) -> u32 {
        self.state.lock().unwrap().config_generation
    }

    fn read_config_space<T: FromBytes>(&self, offset: usize) -> Result<T, Error> {
        assert!(align_of::<T>() <= 4,
            "Driver expected config space alignment of {} bytes, but VirtIO only guarantees 4 byte alignment.",
            align_of::<T>());
        assert!(offset % align_of::<T>() == 0);

        if size_of::<C>() < offset + size_of::<T>() {
            Err(Error::ConfigSpaceTooSmall)
        } else {
            let state = self.state.lock().unwrap();
            let bytes = &state.config_space.as_bytes()[offset..offset + size_of::<T>()];
            Ok(T::read_from_bytes(bytes).unwrap())
        }
    }

    fn write_config_space<T: Immutable + IntoBytes>(
        &mut self,
        offset: usize,
        value: T,
    ) -> Result<(), Error> {
        assert!(align_of::<T>() <= 4,
            "Driver expected config space alignment of {} bytes, but VirtIO only guarantees 4 byte alignment.",
            align_of::<T>());
        assert!(offset % align_of::<T>() == 0);

        if size_of::<C>() < offset + size_of::<T>() {
            Err(Error::ConfigSpaceTooSmall)
        } else {
            let mut state = self.state.lock().unwrap();
            let bytes = &mut state.config_space.as_mut_bytes()[offset..offset + size_of::<T>()];
            value.write_to(bytes).unwrap();
            Ok(())
        }
    }
}

/// The mutable state of a fake transport.
pub struct State<C> {
    /// The status of the fake device.
    pub status: DeviceStatus,
    /// The features which the driver says it supports.
    pub driver_features: u64,
    /// The guest page size set by the driver.
    pub guest_page_size: u32,
    /// Whether the transport has an interrupt pending.
    pub interrupt_pending: bool,
    /// The state of the transport's queues.
    pub queues: Vec<QueueStatus>,
    /// The config generation which the transport should report.
    pub config_generation: u32,
    /// The state of the transport's VirtIO configuration space.
    pub config_space: C,
}

impl<C> Debug for State<C> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("State")
            .field("status", &self.status)
            .field("driver_features", &self.driver_features)
            .field("guest_page_size", &self.guest_page_size)
            .field("interrupt_pending", &self.interrupt_pending)
            .field("queues", &self.queues)
            .field("config_generation", &self.config_generation)
            .field("config_space", &"...")
            .finish()
    }
}

impl<C> State<C> {
    /// Creates a state for a fake transport, with the given queues and VirtIO configuration space.
    pub const fn new(queues: Vec<QueueStatus>, config_space: C) -> Self {
        Self {
            status: DeviceStatus::empty(),
            driver_features: 0,
            guest_page_size: 0,
            interrupt_pending: false,
            queues,
            config_generation: 0,
            config_space,
        }
    }

    /// Simulates the device writing to the given queue.
    ///
    /// The fake device always uses descriptors in order.
    pub fn write_to_queue<const QUEUE_SIZE: usize>(&mut self, queue_index: u16, data: &[u8]) {
        let queue = &self.queues[queue_index as usize];
        assert_ne!(queue.descriptors, 0);
        assert!(fake_read_write_queue(
            queue.descriptors as *const [Descriptor; QUEUE_SIZE],
            queue.driver_area as *const u8,
            queue.device_area as *mut u8,
            |input| {
                assert_eq!(input, Vec::new());
                data.to_owned()
            },
        ));
    }

    /// Simulates the device reading from the given queue.
    ///
    /// Data is read into the `data` buffer passed in. Returns the number of bytes actually read.
    ///
    /// The fake device always uses descriptors in order.
    pub fn read_from_queue<const QUEUE_SIZE: usize>(&mut self, queue_index: u16) -> Vec<u8> {
        let queue = &self.queues[queue_index as usize];
        assert_ne!(queue.descriptors, 0);

        let mut ret = None;

        // Read data from the queue but don't write any response.
        assert!(fake_read_write_queue(
            queue.descriptors as *const [Descriptor; QUEUE_SIZE],
            queue.driver_area as *const u8,
            queue.device_area as *mut u8,
            |input| {
                ret = Some(input);
                Vec::new()
            },
        ));

        ret.unwrap()
    }

    /// Simulates the device reading data from the given queue and then writing a response back.
    ///
    /// The fake device always uses descriptors in order.
    ///
    /// Returns true if a descriptor chain was available and processed, or false if no descriptors were
    /// available.
    pub fn read_write_queue<const QUEUE_SIZE: usize>(
        &mut self,
        queue_index: u16,
        handler: impl FnOnce(Vec<u8>) -> Vec<u8>,
    ) -> bool {
        let queue = &self.queues[queue_index as usize];
        assert_ne!(queue.descriptors, 0);
        fake_read_write_queue(
            queue.descriptors as *const [Descriptor; QUEUE_SIZE],
            queue.driver_area as *const u8,
            queue.device_area as *mut u8,
            handler,
        )
    }

    /// Waits until the given queue is notified.
    pub fn wait_until_queue_notified(state: &Mutex<Self>, queue_index: u16) {
        while !Self::poll_queue_notified(state, queue_index) {
            thread::sleep(Duration::from_millis(10));
        }
    }

    /// Checks if the given queue has been notified.
    ///
    /// If it has, returns true and resets the status so this will return false until it is notified
    /// again.
    pub fn poll_queue_notified(state: &Mutex<Self>, queue_index: u16) -> bool {
        state.lock().unwrap().queues[usize::from(queue_index)]
            .notified
            .swap(false, Ordering::SeqCst)
    }
}

/// The status of a fake virtqueue.
#[derive(Debug, Default)]
pub struct QueueStatus {
    /// The size of the fake virtqueue.
    pub size: u32,
    /// The physical address set for the queue's descriptors.
    pub descriptors: PhysAddr,
    /// The physical address set for the queue's driver area.
    pub driver_area: PhysAddr,
    /// The physical address set for the queue's device area.
    pub device_area: PhysAddr,
    /// Whether the queue has been notified by the driver since last we checked.
    pub notified: AtomicBool,
}
