//! Driver for VirtIO socket devices.
//!
//! To use the driver, you should first create a [`VirtIOSocket`] instance with your VirtIO
//! transport, and then create a [`VsockConnectionManager`] wrapping it to keep track of
//! connections. If you want to manage connections yourself you can use the `VirtIOSocket` directly
//! for a lower-level interface.
//!
//! See [`VsockConnectionManager`] for a usage example.

#[cfg(feature = "alloc")]
mod connectionmanager;
mod error;
mod protocol;
#[cfg(feature = "alloc")]
mod vsock;

#[cfg(feature = "alloc")]
pub use connectionmanager::VsockConnectionManager;
pub use error::SocketError;
pub use protocol::{StreamShutdown, VsockAddr, VMADDR_CID_HOST};
#[cfg(feature = "alloc")]
pub use vsock::{ConnectionInfo, DisconnectReason, VirtIOSocket, VsockEvent, VsockEventType};

/// The size in bytes of each buffer used in the RX virtqueue. This must be bigger than
/// `size_of::<VirtioVsockHdr>()`.
const DEFAULT_RX_BUFFER_SIZE: usize = 512;
