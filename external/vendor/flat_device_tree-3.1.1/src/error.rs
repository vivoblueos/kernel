/// Convenience alias for the library [Result](core::result::Result) type.
pub type Result<T> = core::result::Result<T, Error>;

/// Possible errors when attempting to create an `Fdt`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Error {
    /// The FDT had an invalid magic value.
    BadMagic,
    /// The given pointer was null.
    BadPtr,
    /// Invalid cell encoding.
    BadCell,
    /// Unsupported cell size.
    BadCellSize(usize),
    /// Bad property tag.
    BadPropTag((u32, u32)),
    /// The slice passed in was too small to fit the given total size of the FDT
    /// structure.
    BufferTooSmall,
    /// `cpu` node is missing a `reg` property.
    CpuNoReg,
    /// `cpu` node is missing a `clock-frequency` property.
    CpuNoClockHz,
    /// `cpu` node is missing a `timebase-frequency` property.
    CpuNoTimebaseHz,
    /// `mapped-area` property is missing effective address value.
    MappedNoEffectiveAddr,
    /// `mapped-area` property is missing physical address value.
    MappedNoPhysicalAddr,
    /// `mapped-area` property is missing size value.
    MappedNoSize,
    /// `memory` node missing a `initial-mapped-area` property.
    MemoryNoInitialMapped,
    /// Node missing property.
    MissingProperty,
    /// Missing `root` node.
    MissingRoot,
    /// Missing `chosen` node.
    MissingChosen,
    /// Missing `memory` node.
    MissingMemory,
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Error::BadMagic => write!(f, "bad FDT magic value"),
            Error::BadPtr => write!(f, "an invalid pointer was passed"),
            Error::BadCellSize(cell) => write!(f, "cells of size {cell} are currently unsupported"),
            Error::BadPropTag((have, exp)) => {
                write!(f, "invalid property tag, have: {have}, expected: {exp}")
            }
            Error::BadCell => write!(f, "error parsing the property cell value"),
            Error::BufferTooSmall => {
                write!(f, "the given buffer was too small to contain a FDT header")
            }
            Error::CpuNoReg => {
                write!(f, "`reg` is a required property of `cpu` nodes")
            }
            Error::CpuNoClockHz => {
                write!(f, "`clock-frequency` is a required property of `cpu` nodes")
            }
            Error::CpuNoTimebaseHz => {
                write!(f, "`timebase-frequency` is a required property of `cpu` nodes")
            }
            Error::MappedNoEffectiveAddr => {
                write!(f, "`mapped-area` property is missing effective address value")
            }
            Error::MappedNoPhysicalAddr => {
                write!(f, "`mapped-area` property is missing physical address value")
            }
            Error::MappedNoSize => {
                write!(f, "`mapped-area` property is missing size value")
            }
            Error::MemoryNoInitialMapped => {
                write!(f, "`memory` node is missing an `initial-mapped-area` property")
            }
            Error::MissingProperty => write!(f, "node is missing a property entry"),
            Error::MissingRoot => write!(f, "missing `root` node"),
            Error::MissingChosen => write!(f, "missing `chosen` node"),
            Error::MissingMemory => write!(f, "missing `memory` node"),
        }
    }
}

impl From<Error> for core::fmt::Error {
    fn from(_: Error) -> Self {
        Self
    }
}
