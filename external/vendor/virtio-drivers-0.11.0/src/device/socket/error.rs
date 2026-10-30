//! This module contain the error from the VirtIO socket driver.

use core::result;
use thiserror::Error;

/// The error type of VirtIO socket driver.
#[derive(Copy, Clone, Debug, Eq, Error, PartialEq)]
pub enum SocketError {
    /// There is an existing connection.
    #[error("There is an existing connection. Please close the current connection before attempting to connect again.")]
    ConnectionExists,
    /// The device is not connected to any peer.
    #[error("The device is not connected to any peer. Please connect it to a peer first.")]
    NotConnected,
    /// Peer socket is shutdown.
    #[error("The peer socket is shutdown.")]
    PeerSocketShutdown,
    /// The given buffer is shorter than expected.
    #[error("The given buffer is shorter than expected")]
    BufferTooShort,
    /// The given buffer for output is shorter than expected.
    #[error("The given output buffer is too short. '{0}' bytes is needed for the output buffer.")]
    OutputBufferTooShort(usize),
    /// The given buffer has exceeded the maximum buffer size.
    #[error("The given buffer length '{0}' has exceeded the maximum allowed buffer length '{1}'")]
    BufferTooLong(usize, usize),
    /// Unknown operation.
    #[error("The operation code '{0}' is unknown")]
    UnknownOperation(u16),
    /// Invalid operation,
    #[error("Invalid operation")]
    InvalidOperation,
    /// Invalid number.
    #[error("Invalid number")]
    InvalidNumber,
    /// Unexpected data in packet.
    #[error("No data is expected in the packet")]
    UnexpectedDataInPacket,
    /// Peer has insufficient buffer space, try again later.
    #[error("Peer has insufficient buffer space, try again later")]
    InsufficientBufferSpaceInPeer,
    /// Recycled a wrong buffer.
    #[error("Recycled a wrong buffer")]
    RecycledWrongBuffer,
}

pub type Result<T> = result::Result<T, SocketError>;
