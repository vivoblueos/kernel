//! Types and macros for VirtIO device configuration space.

use crate::{transport::Transport, Error};
use zerocopy::{FromBytes, Immutable, IntoBytes};

/// A configuration space register from which the driver can only read.
#[derive(Default, FromBytes, Immutable, IntoBytes)]
#[repr(transparent)]
pub struct ReadOnly<T: Copy + FromBytes>(pub T);

impl<T: Copy + FromBytes> ReadOnly<T> {
    /// Constructs a new instance for testing.
    pub const fn new(value: T) -> Self {
        Self(value)
    }
}

/// A configuration space register to which the driver can only write.
#[derive(Default, FromBytes, Immutable, IntoBytes)]
#[repr(transparent)]
pub struct WriteOnly<T: Copy + Immutable + IntoBytes>(pub T);

impl<T: Copy + Immutable + IntoBytes> WriteOnly<T> {
    /// Constructs a new instance for testing.
    pub const fn new(value: T) -> Self {
        Self(value)
    }
}

/// A configuration space register which the driver may both read and write.
#[derive(Default, FromBytes, Immutable, IntoBytes)]
#[repr(transparent)]
pub struct ReadWrite<T: Copy + FromBytes + Immutable + IntoBytes>(pub T);

impl<T: Copy + FromBytes + Immutable + IntoBytes> ReadWrite<T> {
    /// Constructs a new instance for testing.
    pub const fn new(value: T) -> Self {
        Self(value)
    }
}

/// Marker trait for configuration space registers from which the driver may read.
pub trait ConfigReadable<T> {}

/// Marker trait for configuration space registers to which the driver may write.
pub trait ConfigWritable<T> {}

impl<T: Copy + FromBytes> ConfigReadable<T> for ReadOnly<T> {}
impl<T: Copy + FromBytes + Immutable + IntoBytes> ConfigReadable<T> for ReadWrite<T> {}
impl<T: Copy + FromBytes + Immutable + IntoBytes> ConfigWritable<T> for ReadWrite<T> {}
impl<T: Copy + Immutable + IntoBytes> ConfigWritable<T> for WriteOnly<T> {}

/// Wrapper for `Transport::read_config_space`` with an extra dummy parameter to force the correct
/// type to be inferred.
#[inline(always)]
pub(crate) fn read_help<T, V, R>(
    transport: &T,
    offset: usize,
    _dummy_r: Option<R>,
) -> Result<V, Error>
where
    T: Transport,
    V: FromBytes + IntoBytes,
    R: ConfigReadable<V>,
{
    transport.read_config_space(offset)
}

/// Wrapper for Transport::write_config_space with an extra dummy parameter to force the correct
/// type to be inferred.
#[inline(always)]
pub(crate) fn write_help<T, V, W>(
    transport: &mut T,
    offset: usize,
    value: V,
    _dummy_w: Option<W>,
) -> Result<(), Error>
where
    T: Transport,
    V: Immutable + IntoBytes,
    W: ConfigWritable<V>,
{
    transport.write_config_space(offset, value)
}

/// Reads the given field of the given struct from the device config space via the given transport.
macro_rules! read_config {
    ($transport:expr, $struct:ty, $field:ident) => {{
        let dummy_struct: Option<$struct> = None;
        let dummy_field = dummy_struct.map(|s| s.$field);
        crate::config::read_help(
            &$transport,
            core::mem::offset_of!($struct, $field),
            dummy_field,
        )
    }};
}

/// Writes the given field of the given struct from the device config space via the given transport.
macro_rules! write_config {
    ($transport:expr, $struct:ty, $field:ident, $value:expr) => {{
        let dummy_struct: Option<$struct> = None;
        let dummy_field = dummy_struct.map(|s| s.$field);
        crate::config::write_help(
            &mut $transport,
            core::mem::offset_of!($struct, $field),
            $value,
            dummy_field,
        )
    }};
}

pub(crate) use read_config;
pub(crate) use write_config;
