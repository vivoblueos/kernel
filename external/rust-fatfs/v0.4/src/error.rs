/// Error enum with all errors that can be returned by functions from this crate
///
/// Generic parameter `T` is a type of external error returned by the user provided storage
#[derive(Debug)]
#[non_exhaustive]
pub enum Error<T> {
    /// A user provided storage instance returned an error during an input/output operation.
    Io(T),
    /// A read operation cannot be completed because an end of a file has been reached prematurely.
    UnexpectedEof,
    /// A write operation cannot be completed because `Write::write` returned 0.
    WriteZero,
    /// A parameter was incorrect.
    InvalidInput,
    /// A requested file or directory has not been found.
    NotFound,
    /// A file or a directory with the same name already exists.
    AlreadyExists,
    /// An operation cannot be finished because a directory is not empty.
    DirectoryIsNotEmpty,
    /// File system internal structures are corrupted/invalid.
    CorruptedFileSystem,
    /// There is not enough free space on the storage to finish the requested operation.
    NotEnoughSpace,
    /// The provided file name is either too long or empty.
    InvalidFileNameLength,
    /// The provided file name contains an invalid character.
    UnsupportedFileNameCharacter,
}

impl<T: IoError> From<T> for Error<T> {
    fn from(error: T) -> Self {
        Error::Io(error)
    }
}

#[cfg(feature = "std")]
impl From<Error<std::io::Error>> for std::io::Error {
    fn from(error: Error<Self>) -> Self {
        match error {
            Error::Io(io_error) => io_error,
            Error::UnexpectedEof | Error::NotEnoughSpace => Self::new(std::io::ErrorKind::UnexpectedEof, error),
            Error::WriteZero => Self::new(std::io::ErrorKind::WriteZero, error),
            Error::InvalidInput
            | Error::InvalidFileNameLength
            | Error::UnsupportedFileNameCharacter
            | Error::DirectoryIsNotEmpty => Self::new(std::io::ErrorKind::InvalidInput, error),
            Error::NotFound => Self::new(std::io::ErrorKind::NotFound, error),
            Error::AlreadyExists => Self::new(std::io::ErrorKind::AlreadyExists, error),
            Error::CorruptedFileSystem => Self::new(std::io::ErrorKind::InvalidData, error),
        }
    }
}

impl<T: core::fmt::Display> core::fmt::Display for Error<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Error::Io(io_error) => write!(f, "IO error: {}", io_error),
            Error::UnexpectedEof => write!(f, "Unexpected end of file"),
            Error::NotEnoughSpace => write!(f, "Not enough space"),
            Error::WriteZero => write!(f, "Write zero"),
            Error::InvalidInput => write!(f, "Invalid input"),
            Error::InvalidFileNameLength => write!(f, "Invalid file name length"),
            Error::UnsupportedFileNameCharacter => write!(f, "Unsupported file name character"),
            Error::DirectoryIsNotEmpty => write!(f, "Directory is not empty"),
            Error::NotFound => write!(f, "No such file or directory"),
            Error::AlreadyExists => write!(f, "File or directory already exists"),
            Error::CorruptedFileSystem => write!(f, "Corrupted file system"),
        }
    }
}

#[cfg(feature = "std")]
impl<T: std::error::Error + 'static> std::error::Error for Error<T> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        if let Error::Io(io_error) = self {
            Some(io_error)
        } else {
            None
        }
    }
}

/// Trait that should be implemented by errors returned from the user supplied storage.
///
/// Implementations for `std::io::Error` and `()` are provided by this crate.
pub trait IoError: core::fmt::Debug {
    fn is_interrupted(&self) -> bool;
    fn new_unexpected_eof_error() -> Self;
    fn new_write_zero_error() -> Self;
}

impl<T: core::fmt::Debug + IoError> IoError for Error<T> {
    fn is_interrupted(&self) -> bool {
        match self {
            Error::<T>::Io(io_error) => io_error.is_interrupted(),
            _ => false,
        }
    }

    fn new_unexpected_eof_error() -> Self {
        Error::<T>::UnexpectedEof
    }

    fn new_write_zero_error() -> Self {
        Error::<T>::WriteZero
    }
}

impl IoError for () {
    fn is_interrupted(&self) -> bool {
        false
    }

    fn new_unexpected_eof_error() -> Self {
        // empty
    }

    fn new_write_zero_error() -> Self {
        // empty
    }
}

#[cfg(feature = "std")]
impl IoError for std::io::Error {
    fn is_interrupted(&self) -> bool {
        self.kind() == std::io::ErrorKind::Interrupted
    }

    fn new_unexpected_eof_error() -> Self {
        Self::new(std::io::ErrorKind::UnexpectedEof, "failed to fill whole buffer")
    }

    fn new_write_zero_error() -> Self {
        Self::new(std::io::ErrorKind::WriteZero, "failed to write whole buffer")
    }
}
