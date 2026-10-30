//! Driver for VirtIO console devices.

#[cfg(feature = "embedded-io")]
mod embedded_io;

use crate::config::{read_config, write_config, ReadOnly, WriteOnly};
use crate::hal::Hal;
use crate::queue::VirtQueue;
use crate::transport::Transport;
use crate::{Error, Result, PAGE_SIZE};
use alloc::boxed::Box;
use bitflags::bitflags;
use core::fmt::{self, Display, Formatter, Write};
use log::error;
use zerocopy::{FromBytes, Immutable, IntoBytes};

const QUEUE_RECEIVEQ_PORT_0: u16 = 0;
const QUEUE_TRANSMITQ_PORT_0: u16 = 1;
const QUEUE_SIZE: usize = 2;
const SUPPORTED_FEATURES: Features = Features::RING_EVENT_IDX
    .union(Features::RING_INDIRECT_DESC)
    .union(Features::SIZE)
    .union(Features::EMERG_WRITE);

/// Driver for a VirtIO console device.
///
/// Only a single port is supported.
///
/// # Example
///
/// ```
/// # use virtio_drivers::{Error, Hal, transport::Transport};
/// use virtio_drivers::device::console::VirtIOConsole;
/// # fn example<HalImpl: Hal, T: Transport>(transport: T) -> Result<(), Error> {
/// let mut console = VirtIOConsole::<HalImpl, _>::new(transport)?;
///
/// let size = console.size().unwrap().unwrap();
/// println!("VirtIO console {}x{}", size.rows, size.columns);
///
/// for &c in b"Hello console!\n" {
///   console.send(c)?;
/// }
///
/// let c = console.recv(true)?;
/// println!("Read {:?} from console.", c);
/// # Ok(())
/// # }
/// ```
pub struct VirtIOConsole<H: Hal, T: Transport> {
    transport: T,
    negotiated_features: Features,
    receiveq: VirtQueue<H, QUEUE_SIZE>,
    transmitq: VirtQueue<H, QUEUE_SIZE>,
    queue_buf_rx: Box<[u8; PAGE_SIZE]>,
    /// The index of the next byte in `queue_buf_rx` which `recv` should return.
    cursor: usize,
    /// The number of bytes read into `queue_buf_rx`.
    pending_len: usize,
    /// The token of the outstanding receive request, if there is one.
    receive_token: Option<u16>,
}

// SAFETY: The config space can be accessed from any thread.
unsafe impl<H: Hal, T: Transport + Send> Send for VirtIOConsole<H, T> where
    VirtQueue<H, QUEUE_SIZE>: Send
{
}

// SAFETY: A `&VirtIOConsole` only allows reading the config space.
unsafe impl<H: Hal, T: Transport + Sync> Sync for VirtIOConsole<H, T> where
    VirtQueue<H, QUEUE_SIZE>: Sync
{
}

/// The width and height of a console, in characters.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub struct Size {
    /// The console width in characters.
    pub columns: u16,
    /// The console height in characters.
    pub rows: u16,
}

impl Display for Size {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}x{}", self.columns, self.rows)
    }
}

impl<H: Hal, T: Transport> VirtIOConsole<H, T> {
    /// Creates a new VirtIO console driver.
    pub fn new(mut transport: T) -> Result<Self> {
        let negotiated_features = transport.begin_init(SUPPORTED_FEATURES);
        let receiveq = VirtQueue::new(
            &mut transport,
            QUEUE_RECEIVEQ_PORT_0,
            negotiated_features.contains(Features::RING_INDIRECT_DESC),
            negotiated_features.contains(Features::RING_EVENT_IDX),
        )?;
        let transmitq = VirtQueue::new(
            &mut transport,
            QUEUE_TRANSMITQ_PORT_0,
            negotiated_features.contains(Features::RING_INDIRECT_DESC),
            negotiated_features.contains(Features::RING_EVENT_IDX),
        )?;

        // Safe because no alignment or initialisation is required for [u8], the DMA buffer is
        // dereferenceable, and the lifetime of the reference matches the lifetime of the DMA buffer
        // (which we don't otherwise access).
        let queue_buf_rx = Box::new([0; PAGE_SIZE]);

        transport.finish_init();
        let mut console = VirtIOConsole {
            transport,
            negotiated_features,
            receiveq,
            transmitq,
            queue_buf_rx,
            cursor: 0,
            pending_len: 0,
            receive_token: None,
        };
        console.poll_retrieve()?;
        Ok(console)
    }

    /// Returns the size of the console, if the device supports reporting this.
    pub fn size(&self) -> Result<Option<Size>> {
        if self.negotiated_features.contains(Features::SIZE) {
            self.transport.read_consistent(|| {
                Ok(Some(Size {
                    columns: read_config!(self.transport, Config, cols)?,
                    rows: read_config!(self.transport, Config, rows)?,
                }))
            })
        } else {
            Ok(None)
        }
    }

    /// Makes a request to the device to receive data, if there is not already an outstanding
    /// receive request or some data already received and not yet returned.
    fn poll_retrieve(&mut self) -> Result<()> {
        if self.receive_token.is_none() && self.cursor == self.pending_len {
            // SAFETY: The buffer lasts at least as long as the queue, and there are no other
            // outstanding requests using the buffer.
            self.receive_token = Some(unsafe {
                self.receiveq
                    .add(&[], &mut [self.queue_buf_rx.as_mut_slice()])
            }?);
            if self.receiveq.should_notify() {
                self.transport.notify(QUEUE_RECEIVEQ_PORT_0);
            }
        }
        Ok(())
    }

    /// Acknowledges a pending interrupt, if any, and completes the outstanding finished read
    /// request if there is one.
    ///
    /// Returns true if new data has been received.
    pub fn ack_interrupt(&mut self) -> Result<bool> {
        if !self.transport.ack_interrupt() {
            return Ok(false);
        }

        self.finish_receive()
    }

    /// If there is an outstanding receive request and it has finished, completes it.
    ///
    /// Returns true if new data has been received.
    fn finish_receive(&mut self) -> Result<bool> {
        let mut flag = false;
        if let Some(receive_token) = self.receive_token {
            if self.receive_token == self.receiveq.peek_used() {
                // SAFETY: We are passing the same buffer as we passed to `VirtQueue::add` in
                // `poll_retrieve` and it is still valid.
                let len = unsafe {
                    self.receiveq.pop_used(
                        receive_token,
                        &[],
                        &mut [self.queue_buf_rx.as_mut_slice()],
                    )?
                };
                flag = true;
                assert_ne!(len, 0);
                self.cursor = 0;
                self.pending_len = len as usize;
                // Clear `receive_token` so that when the buffer is used up the next call to
                // `poll_retrieve` will add a new pending request.
                self.receive_token.take();
            }
        }
        Ok(flag)
    }

    /// Returns the next available character from the console, if any.
    ///
    /// If no data has been received this will not block but immediately return `Ok<None>`.
    pub fn recv(&mut self, pop: bool) -> Result<Option<u8>> {
        self.finish_receive()?;
        if self.cursor == self.pending_len {
            return Ok(None);
        }
        let ch = self.queue_buf_rx[self.cursor];
        if pop {
            self.cursor += 1;
            self.poll_retrieve()?;
        }
        Ok(Some(ch))
    }

    /// Sends a character to the console.
    pub fn send(&mut self, chr: u8) -> Result<()> {
        let buf: [u8; 1] = [chr];
        self.transmitq
            .add_notify_wait_pop(&[&buf], &mut [], &mut self.transport)?;
        Ok(())
    }

    /// Sends one or more bytes to the console.
    pub fn send_bytes(&mut self, buffer: &[u8]) -> Result {
        self.transmitq
            .add_notify_wait_pop(&[buffer], &mut [], &mut self.transport)?;
        Ok(())
    }

    /// Blocks until at least one character is available to read.
    fn wait_for_receive(&mut self) -> Result {
        self.poll_retrieve()?;
        while self.cursor == self.pending_len {
            self.finish_receive()?;
        }
        Ok(())
    }

    /// Sends a character to the console using the emergency write feature.
    ///
    /// Returns an error if the device doesn't support emergency write.
    pub fn emergency_write(&mut self, chr: u8) -> Result<()> {
        if self.negotiated_features.contains(Features::EMERG_WRITE) {
            write_config!(self.transport, Config, emerg_wr, chr.into())?;
            Ok(())
        } else {
            Err(Error::Unsupported)
        }
    }
}

impl<H: Hal, T: Transport> Write for VirtIOConsole<H, T> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        self.send_bytes(s.as_bytes()).map_err(|e| {
            error!("Error writing to conosel: {}", e);
            fmt::Error
        })
    }
}

impl<H: Hal, T: Transport> Drop for VirtIOConsole<H, T> {
    fn drop(&mut self) {
        // Clear any pointers pointing to DMA regions, so the device doesn't try to access them
        // after they have been freed.
        self.transport.queue_unset(QUEUE_RECEIVEQ_PORT_0);
        self.transport.queue_unset(QUEUE_TRANSMITQ_PORT_0);
    }
}

#[derive(FromBytes, Immutable, IntoBytes)]
#[repr(C)]
struct Config {
    cols: ReadOnly<u16>,
    rows: ReadOnly<u16>,
    max_nr_ports: ReadOnly<u32>,
    emerg_wr: WriteOnly<u32>,
}

bitflags! {
    #[derive(Copy, Clone, Debug, Default, Eq, PartialEq)]
    struct Features: u64 {
        const SIZE                  = 1 << 0;
        const MULTIPORT             = 1 << 1;
        const EMERG_WRITE           = 1 << 2;

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
    use std::{sync::Mutex, thread};

    #[test]
    fn config_info_no_features() {
        let config_space = Config {
            cols: ReadOnly::new(80),
            rows: ReadOnly::new(42),
            max_nr_ports: ReadOnly::new(0),
            emerg_wr: WriteOnly::default(),
        };
        let state = Arc::new(Mutex::new(State::new(
            vec![QueueStatus::default(), QueueStatus::default()],
            config_space,
        )));
        let transport = FakeTransport {
            device_type: DeviceType::Console,
            max_queue_size: 2,
            device_features: 0,
            state: state.clone(),
        };
        let console = VirtIOConsole::<FakeHal, FakeTransport<Config>>::new(transport).unwrap();

        assert_eq!(console.size(), Ok(None));
    }

    #[test]
    fn config_info() {
        let config_space = Config {
            cols: ReadOnly::new(80),
            rows: ReadOnly::new(42),
            max_nr_ports: ReadOnly::new(0),
            emerg_wr: WriteOnly::default(),
        };
        let state = Arc::new(Mutex::new(State::new(
            vec![QueueStatus::default(), QueueStatus::default()],
            config_space,
        )));
        let transport = FakeTransport {
            device_type: DeviceType::Console,
            max_queue_size: 2,
            device_features: 0x07,
            state: state.clone(),
        };
        let console = VirtIOConsole::<FakeHal, FakeTransport<Config>>::new(transport).unwrap();

        assert_eq!(
            console.size(),
            Ok(Some(Size {
                columns: 80,
                rows: 42
            }))
        );
    }

    #[test]
    fn emergency_write() {
        let config_space = Config {
            cols: ReadOnly::new(0),
            rows: ReadOnly::new(0),
            max_nr_ports: ReadOnly::new(0),
            emerg_wr: WriteOnly::default(),
        };
        let state = Arc::new(Mutex::new(State::new(
            vec![QueueStatus::default(), QueueStatus::default()],
            config_space,
        )));
        let transport = FakeTransport {
            device_type: DeviceType::Console,
            max_queue_size: 2,
            device_features: 0x07,
            state: state.clone(),
        };
        let mut console = VirtIOConsole::<FakeHal, FakeTransport<Config>>::new(transport).unwrap();

        console.emergency_write(42).unwrap();
        assert_eq!(state.lock().unwrap().config_space.emerg_wr.0, 42);
    }

    #[test]
    fn receive() {
        let config_space = Config {
            cols: ReadOnly::new(0),
            rows: ReadOnly::new(0),
            max_nr_ports: ReadOnly::new(0),
            emerg_wr: WriteOnly::default(),
        };
        let state = Arc::new(Mutex::new(State::new(
            vec![QueueStatus::default(), QueueStatus::default()],
            config_space,
        )));
        let transport = FakeTransport {
            device_type: DeviceType::Console,
            max_queue_size: 2,
            device_features: 0,
            state: state.clone(),
        };
        let mut console = VirtIOConsole::<FakeHal, FakeTransport<Config>>::new(transport).unwrap();

        // Nothing is available to receive.
        assert_eq!(console.recv(false).unwrap(), None);
        assert_eq!(console.recv(true).unwrap(), None);

        // Still nothing after a spurious interrupt.
        assert_eq!(console.ack_interrupt(), Ok(false));
        assert_eq!(console.recv(false).unwrap(), None);

        // Make a character available, and simulate an interrupt.
        {
            let mut state = state.lock().unwrap();
            state.write_to_queue::<QUEUE_SIZE>(QUEUE_RECEIVEQ_PORT_0, &[42]);

            state.interrupt_pending = true;
        }
        assert_eq!(console.ack_interrupt(), Ok(true));
        assert_eq!(state.lock().unwrap().interrupt_pending, false);

        // Receive the character. If we don't pop it it is still there to read again.
        assert_eq!(console.recv(false).unwrap(), Some(42));
        assert_eq!(console.recv(true).unwrap(), Some(42));
        assert_eq!(console.recv(true).unwrap(), None);
    }

    #[test]
    fn send() {
        let config_space = Config {
            cols: ReadOnly::new(0),
            rows: ReadOnly::new(0),
            max_nr_ports: ReadOnly::new(0),
            emerg_wr: WriteOnly::default(),
        };
        let state = Arc::new(Mutex::new(State::new(
            vec![QueueStatus::default(), QueueStatus::default()],
            config_space,
        )));
        let transport = FakeTransport {
            device_type: DeviceType::Console,
            max_queue_size: 2,
            device_features: 0,
            state: state.clone(),
        };
        let mut console = VirtIOConsole::<FakeHal, FakeTransport<Config>>::new(transport).unwrap();

        // Start a thread to simulate the device waiting for characters.
        let handle = thread::spawn(move || {
            println!("Device waiting for a character.");
            State::wait_until_queue_notified(&state, QUEUE_TRANSMITQ_PORT_0);
            println!("Transmit queue was notified.");

            let data = state
                .lock()
                .unwrap()
                .read_from_queue::<QUEUE_SIZE>(QUEUE_TRANSMITQ_PORT_0);
            assert_eq!(data, b"Q");
        });

        assert_eq!(console.send(b'Q'), Ok(()));

        handle.join().unwrap();
    }
}
