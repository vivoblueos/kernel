//! Driver for VirtIO input devices.

use super::common::Feature;
use crate::config::{read_config, write_config, ReadOnly, WriteOnly};
use crate::hal::Hal;
use crate::queue::VirtQueue;
use crate::transport::Transport;
use crate::Error;
use alloc::{boxed::Box, string::String};
use core::cmp::min;
use core::mem::{offset_of, size_of};
use zerocopy::{FromBytes, FromZeros, Immutable, IntoBytes, KnownLayout};

/// Virtual human interface devices such as keyboards, mice and tablets.
///
/// An instance of the virtio device represents one such input device.
/// Device behavior mirrors that of the evdev layer in Linux,
/// making pass-through implementations on top of evdev easy.
pub struct VirtIOInput<H: Hal, T: Transport> {
    transport: T,
    event_queue: VirtQueue<H, QUEUE_SIZE>,
    status_queue: VirtQueue<H, QUEUE_SIZE>,
    event_buf: Box<[InputEvent; 32]>,
}

impl<H: Hal, T: Transport> VirtIOInput<H, T> {
    /// Create a new VirtIO-Input driver.
    pub fn new(mut transport: T) -> Result<Self, Error> {
        let mut event_buf = Box::new([InputEvent::default(); QUEUE_SIZE]);

        let negotiated_features = transport.begin_init(SUPPORTED_FEATURES);

        let mut event_queue = VirtQueue::new(
            &mut transport,
            QUEUE_EVENT,
            negotiated_features.contains(Feature::RING_INDIRECT_DESC),
            negotiated_features.contains(Feature::RING_EVENT_IDX),
        )?;
        let status_queue = VirtQueue::new(
            &mut transport,
            QUEUE_STATUS,
            negotiated_features.contains(Feature::RING_INDIRECT_DESC),
            negotiated_features.contains(Feature::RING_EVENT_IDX),
        )?;
        for (i, event) in event_buf.as_mut().iter_mut().enumerate() {
            // SAFETY: The buffer lasts as long as the queue.
            let token = unsafe { event_queue.add(&[], &mut [event.as_mut_bytes()])? };
            assert_eq!(token, i as u16);
        }
        if event_queue.should_notify() {
            transport.notify(QUEUE_EVENT);
        }

        transport.finish_init();

        Ok(VirtIOInput {
            transport,
            event_queue,
            status_queue,
            event_buf,
        })
    }

    /// Acknowledge interrupt and process events.
    pub fn ack_interrupt(&mut self) -> bool {
        self.transport.ack_interrupt()
    }

    /// Pop the pending event.
    pub fn pop_pending_event(&mut self) -> Option<InputEvent> {
        if let Some(token) = self.event_queue.peek_used() {
            let event = &mut self.event_buf[token as usize];
            // SAFETY: We are passing the same buffer as we passed to `VirtQueue::add` and it is still valid.
            unsafe {
                self.event_queue
                    .pop_used(token, &[], &mut [event.as_mut_bytes()])
                    .ok()?;
            }
            let event_saved = *event;
            // requeue
            // SAFETY: The buffer lasts as long as the queue.
            if let Ok(new_token) = unsafe { self.event_queue.add(&[], &mut [event.as_mut_bytes()]) }
            {
                // This only works because nothing happen between `pop_used` and `add` that affects
                // the list of free descriptors in the queue, so `add` reuses the descriptor which
                // was just freed by `pop_used`.
                assert_eq!(new_token, token);
                if self.event_queue.should_notify() {
                    self.transport.notify(QUEUE_EVENT);
                }
                return Some(event_saved);
            }
        }
        None
    }

    /// Query a specific piece of information by `select` and `subsel`, and write
    /// result to `out`, return the result size.
    pub fn query_config_select(
        &mut self,
        select: InputConfigSelect,
        subsel: u8,
        out: &mut [u8],
    ) -> Result<u8, Error> {
        write_config!(self.transport, Config, select, select as u8)?;
        write_config!(self.transport, Config, subsel, subsel)?;
        let size: u8 = read_config!(self.transport, Config, size)?;
        // Safe because config points to a valid MMIO region for the config space.
        let size_to_copy = min(usize::from(size), out.len());
        for (i, out_item) in out.iter_mut().take(size_to_copy).enumerate() {
            *out_item = self
                .transport
                .read_config_space(offset_of!(Config, data) + i * size_of::<u8>())?;
        }

        Ok(size)
    }

    /// Queries a specific piece of information by `select` and `subsel`, allocates a sufficiently
    /// large byte buffer for it, and returns it.
    fn query_config_select_alloc(
        &mut self,
        select: InputConfigSelect,
        subsel: u8,
    ) -> Result<Box<[u8]>, Error> {
        write_config!(self.transport, Config, select, select as u8)?;
        write_config!(self.transport, Config, subsel, subsel)?;
        let size = usize::from(read_config!(self.transport, Config, size)?);
        if size > CONFIG_DATA_MAX_LENGTH {
            return Err(Error::IoError);
        }
        let mut buf = <[u8]>::new_box_zeroed_with_elems(size).unwrap();
        for i in 0..size {
            buf[i] = self
                .transport
                .read_config_space(offset_of!(Config, data) + i * size_of::<u8>())?;
        }
        Ok(buf)
    }

    /// Queries a specific piece of information by `select` and `subsel` into a newly-allocated
    /// buffer, and tries to convert it to a string.
    ///
    /// Returns an error if it is not valid UTF-8.
    fn query_config_string(
        &mut self,
        select: InputConfigSelect,
        subsel: u8,
    ) -> Result<String, Error> {
        Ok(String::from_utf8(
            self.query_config_select_alloc(select, subsel)?.into(),
        )?)
    }

    /// Queries and returns the name of the device, or an error if it is not valid UTF-8.
    pub fn name(&mut self) -> Result<String, Error> {
        self.query_config_string(InputConfigSelect::IdName, 0)
    }

    /// Queries and returns the serial number of the device, or an error if it is not valid UTF-8.
    pub fn serial_number(&mut self) -> Result<String, Error> {
        self.query_config_string(InputConfigSelect::IdSerial, 0)
    }

    /// Queries and returns the ID information of the device.
    pub fn ids(&mut self) -> Result<DevIDs, Error> {
        let mut ids = DevIDs::default();
        let size = self.query_config_select(InputConfigSelect::IdDevids, 0, ids.as_mut_bytes())?;
        if usize::from(size) == size_of::<DevIDs>() {
            Ok(ids)
        } else {
            Err(Error::IoError)
        }
    }

    /// Queries and returns the input properties of the device.
    pub fn prop_bits(&mut self) -> Result<Box<[u8]>, Error> {
        self.query_config_select_alloc(InputConfigSelect::PropBits, 0)
    }

    /// Queries and returns a bitmap of supported event codes for the given event type.
    ///
    /// If the event type is not supported an empty slice will be returned.
    pub fn ev_bits(&mut self, event_type: u8) -> Result<Box<[u8]>, Error> {
        self.query_config_select_alloc(InputConfigSelect::EvBits, event_type)
    }

    /// Queries and returns information about the given axis of the device.
    pub fn abs_info(&mut self, axis: u8) -> Result<AbsInfo, Error> {
        let mut info = AbsInfo::default();
        let size =
            self.query_config_select(InputConfigSelect::AbsInfo, axis, info.as_mut_bytes())?;
        if usize::from(size) == size_of::<AbsInfo>() {
            Ok(info)
        } else {
            Err(Error::IoError)
        }
    }
}

// SAFETY: The config space can be accessed from any thread.
unsafe impl<H: Hal, T: Transport + Send> Send for VirtIOInput<H, T> where
    VirtQueue<H, QUEUE_SIZE>: Send
{
}

// SAFETY: An '&VirtIOInput` can't do anything, all methods take `&mut self`.
unsafe impl<H: Hal, T: Transport + Sync> Sync for VirtIOInput<H, T> where
    VirtQueue<H, QUEUE_SIZE>: Sync
{
}

impl<H: Hal, T: Transport> Drop for VirtIOInput<H, T> {
    fn drop(&mut self) {
        // Clear any pointers pointing to DMA regions, so the device doesn't try to access them
        // after they have been freed.
        self.transport.queue_unset(QUEUE_EVENT);
        self.transport.queue_unset(QUEUE_STATUS);
    }
}

const CONFIG_DATA_MAX_LENGTH: usize = 128;

/// Select value used for [`VirtIOInput::query_config_select()`].
#[repr(u8)]
#[derive(Debug, Clone, Copy)]
pub enum InputConfigSelect {
    /// Returns the name of the device, in u.string. subsel is zero.
    IdName = 0x01,
    /// Returns the serial number of the device, in u.string. subsel is zero.
    IdSerial = 0x02,
    /// Returns ID information of the device, in u.ids. subsel is zero.
    IdDevids = 0x03,
    /// Returns input properties of the device, in u.bitmap. subsel is zero.
    /// Individual bits in the bitmap correspond to INPUT_PROP_* constants used
    /// by the underlying evdev implementation.
    PropBits = 0x10,
    /// subsel specifies the event type using EV_* constants in the underlying
    /// evdev implementation. If size is non-zero the event type is supported
    /// and a bitmap of supported event codes is returned in u.bitmap. Individual
    /// bits in the bitmap correspond to implementation-defined input event codes,
    /// for example keys or pointing device axes.
    EvBits = 0x11,
    /// subsel specifies the absolute axis using ABS_* constants in the underlying
    /// evdev implementation. Information about the axis will be returned in u.abs.
    AbsInfo = 0x12,
}

#[derive(FromBytes, Immutable, IntoBytes)]
#[repr(C)]
struct Config {
    select: WriteOnly<u8>,
    subsel: WriteOnly<u8>,
    size: ReadOnly<u8>,
    _reserved: [ReadOnly<u8>; 5],
    data: [ReadOnly<u8>; CONFIG_DATA_MAX_LENGTH],
}

/// Information about an axis of an input device, typically a joystick.
#[repr(C)]
#[derive(Clone, Debug, Default, Eq, FromBytes, Immutable, IntoBytes, KnownLayout, PartialEq)]
pub struct AbsInfo {
    /// The minimum value for the axis.
    pub min: u32,
    /// The maximum value for the axis.
    pub max: u32,
    /// The fuzz value used to filter noise from the event stream.
    pub fuzz: u32,
    /// The size of the dead zone; values less than this will be reported as 0.
    pub flat: u32,
    /// The resolution for values reported for the axis.
    pub res: u32,
}

/// The identifiers of a VirtIO input device.
#[repr(C)]
#[derive(Clone, Debug, Default, Eq, FromBytes, Immutable, IntoBytes, KnownLayout, PartialEq)]
pub struct DevIDs {
    /// The bustype identifier.
    pub bustype: u16,
    /// The vendor identifier.
    pub vendor: u16,
    /// The product identifier.
    pub product: u16,
    /// The version identifier.
    pub version: u16,
}

/// Both queues use the same `virtio_input_event` struct. `type`, `code` and `value`
/// are filled according to the Linux input layer (evdev) interface.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, FromBytes, Immutable, IntoBytes, KnownLayout)]
pub struct InputEvent {
    /// Event type.
    pub event_type: u16,
    /// Event code.
    pub code: u16,
    /// Event value.
    pub value: u32,
}

const QUEUE_EVENT: u16 = 0;
const QUEUE_STATUS: u16 = 1;
const SUPPORTED_FEATURES: Feature = Feature::RING_EVENT_IDX.union(Feature::RING_INDIRECT_DESC);

// a parameter that can change
const QUEUE_SIZE: usize = 32;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        hal::fake::FakeHal,
        transport::{
            fake::{FakeTransport, QueueStatus, State},
            DeviceType,
        },
    };
    use alloc::{sync::Arc, vec};
    use core::convert::TryInto;
    use std::sync::Mutex;

    #[test]
    fn config() {
        const DEFAULT_DATA: ReadOnly<u8> = ReadOnly::new(0);
        let config_space = Config {
            select: WriteOnly::default(),
            subsel: WriteOnly::default(),
            size: ReadOnly::new(0),
            _reserved: Default::default(),
            data: [DEFAULT_DATA; 128],
        };
        let state = Arc::new(Mutex::new(State::new(
            vec![QueueStatus::default(), QueueStatus::default()],
            config_space,
        )));
        let transport = FakeTransport {
            device_type: DeviceType::Block,
            max_queue_size: QUEUE_SIZE.try_into().unwrap(),
            device_features: 0,
            state: state.clone(),
        };
        let mut input = VirtIOInput::<FakeHal, FakeTransport<Config>>::new(transport).unwrap();

        set_data(
            &mut state.lock().unwrap().config_space,
            "Test input device".as_bytes(),
        );
        assert_eq!(input.name().unwrap(), "Test input device");
        assert_eq!(
            state.lock().unwrap().config_space.select.0,
            InputConfigSelect::IdName as u8
        );
        assert_eq!(state.lock().unwrap().config_space.subsel.0, 0);

        set_data(
            &mut state.lock().unwrap().config_space,
            "Serial number".as_bytes(),
        );
        assert_eq!(input.serial_number().unwrap(), "Serial number");
        assert_eq!(
            state.lock().unwrap().config_space.select.0,
            InputConfigSelect::IdSerial as u8
        );
        assert_eq!(state.lock().unwrap().config_space.subsel.0, 0);

        let ids = DevIDs {
            bustype: 0x4242,
            product: 0x0067,
            vendor: 0x1234,
            version: 0x4321,
        };
        set_data(&mut state.lock().unwrap().config_space, ids.as_bytes());
        assert_eq!(input.ids().unwrap(), ids);
        assert_eq!(
            state.lock().unwrap().config_space.select.0,
            InputConfigSelect::IdDevids as u8
        );
        assert_eq!(state.lock().unwrap().config_space.subsel.0, 0);

        set_data(&mut state.lock().unwrap().config_space, &[0x12, 0x34, 0x56]);
        assert_eq!(input.prop_bits().unwrap().as_ref(), &[0x12, 0x34, 0x56]);
        assert_eq!(
            state.lock().unwrap().config_space.select.0,
            InputConfigSelect::PropBits as u8
        );
        assert_eq!(state.lock().unwrap().config_space.subsel.0, 0);

        set_data(&mut state.lock().unwrap().config_space, &[0x42, 0x66]);
        assert_eq!(input.ev_bits(3).unwrap().as_ref(), &[0x42, 0x66]);
        assert_eq!(
            state.lock().unwrap().config_space.select.0,
            InputConfigSelect::EvBits as u8
        );
        assert_eq!(state.lock().unwrap().config_space.subsel.0, 3);

        let abs_info = AbsInfo {
            min: 12,
            max: 1234,
            fuzz: 4,
            flat: 10,
            res: 2,
        };
        set_data(&mut state.lock().unwrap().config_space, abs_info.as_bytes());
        assert_eq!(input.abs_info(5).unwrap(), abs_info);
        assert_eq!(
            state.lock().unwrap().config_space.select.0,
            InputConfigSelect::AbsInfo as u8
        );
        assert_eq!(state.lock().unwrap().config_space.subsel.0, 5);
    }

    fn set_data(config_space: &mut Config, value: &[u8]) {
        config_space.size.0 = value.len().try_into().unwrap();
        for (i, &byte) in value.into_iter().enumerate() {
            config_space.data[i].0 = byte;
        }
    }
}
