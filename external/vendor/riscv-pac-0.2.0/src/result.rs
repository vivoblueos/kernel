use core::fmt;

/// Convenience alias for the [Result](core::result::Result) type for the library.
pub type Result<T> = core::result::Result<T, Error>;

/// Represents error variants for the library.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Error {
    /// Attempted out-of-bounds access.
    IndexOutOfBounds {
        index: usize,
        min: usize,
        max: usize,
    },
    /// Invalid field value.
    InvalidFieldValue {
        field: &'static str,
        value: usize,
        bitmask: usize,
    },
    /// Invalid value of a register field that does not match any known variants.
    InvalidFieldVariant { field: &'static str, value: usize },
    /// Invalid value.
    InvalidValue { value: usize, bitmask: usize },
    /// Invalid value that does not match any known variants.
    InvalidVariant(usize),
    /// Unimplemented function or type.
    Unimplemented,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::IndexOutOfBounds { index, min, max } => write!(
                f,
                "out-of-bounds access, index: {index}, min: {min}, max: {max}"
            ),
            Self::InvalidFieldValue {
                field,
                value,
                bitmask,
            } => write!(
                f,
                "invalid {field} field value: {value:#x}, valid bitmask: {bitmask:#x}",
            ),
            Self::InvalidFieldVariant { field, value } => {
                write!(f, "invalid {field} field variant: {value:#x}")
            }
            Self::InvalidValue { value, bitmask } => {
                write!(f, "invalid value: {value:#x}, valid bitmask: {bitmask:#x}",)
            }
            Self::InvalidVariant(value) => {
                write!(f, "invalid variant: {value:#x}")
            }
            Self::Unimplemented => write!(f, "unimplemented"),
        }
    }
}
