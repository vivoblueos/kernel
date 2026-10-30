//! Implementation of `embedded-io::Error' trait for `Error`.

use crate::{device::socket::SocketError, Error};
use embedded_io::ErrorKind;

impl embedded_io::Error for Error {
    fn kind(&self) -> ErrorKind {
        match self {
            Error::InvalidParam => ErrorKind::InvalidInput,
            Error::DmaError => ErrorKind::OutOfMemory,
            Error::Unsupported => ErrorKind::Unsupported,
            Error::SocketDeviceError(e) => match e {
                &SocketError::ConnectionExists => ErrorKind::AddrInUse,
                SocketError::NotConnected => ErrorKind::NotConnected,
                SocketError::PeerSocketShutdown => ErrorKind::ConnectionAborted,
                SocketError::BufferTooShort => ErrorKind::InvalidInput,
                SocketError::OutputBufferTooShort(_) => ErrorKind::InvalidInput,
                SocketError::BufferTooLong(_, _) => ErrorKind::InvalidInput,
                SocketError::InsufficientBufferSpaceInPeer => ErrorKind::WriteZero,
                SocketError::UnknownOperation(_)
                | SocketError::InvalidOperation
                | SocketError::InvalidNumber
                | SocketError::UnexpectedDataInPacket
                | SocketError::RecycledWrongBuffer => ErrorKind::Other,
            },
            Error::QueueFull
            | Error::NotReady
            | Error::WrongToken
            | Error::AlreadyUsed
            | Error::IoError
            | Error::ConfigSpaceTooSmall
            | Error::ConfigSpaceMissing => ErrorKind::Other,
        }
    }
}
