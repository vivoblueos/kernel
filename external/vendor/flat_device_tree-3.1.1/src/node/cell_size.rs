/// Represents the cell size of a property value.
#[repr(u8)]
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CellSize {
    None = 0,
    One = 1,
    Two = 2,
    Three = 3,
}

impl CellSize {
    /// Creates a new [CellSize].
    pub const fn new() -> Self {
        Self::One
    }

    /// Infallible function that converts a [`u8`] into a [CellSize].
    pub const fn from_u8(val: u8) -> Self {
        match val {
            1 => Self::One,
            2 => Self::Two,
            3 => Self::Three,
            _ => Self::None,
        }
    }

    /// Infallible function that converts a [`u16`] into a [CellSize].
    pub const fn from_u16(val: u16) -> Self {
        Self::from_u8(val as u8)
    }

    /// Infallible function that converts a [`u32`] into a [CellSize].
    pub const fn from_u32(val: u32) -> Self {
        Self::from_u8(val as u8)
    }

    /// Infallible function that converts a [`u64`] into a [CellSize].
    pub const fn from_u64(val: u64) -> Self {
        Self::from_u8(val as u8)
    }

    /// Infallible function that converts a [`usize`] into a [CellSize].
    pub const fn from_usize(val: usize) -> Self {
        Self::from_u8(val as u8)
    }

    /// Converts a [CellSize] into a [`u8`].
    pub const fn to_u8(self) -> u8 {
        self as u8
    }

    /// Converts a [CellSize] into a [`u16`].
    pub const fn to_u16(self) -> u16 {
        self as u16
    }

    /// Converts a [CellSize] into a [`u32`].
    pub const fn to_u32(self) -> u32 {
        self as u32
    }

    /// Converts a [CellSize] into a [`u64`].
    pub const fn to_u64(self) -> u64 {
        self as u64
    }

    /// Converts a [CellSize] into a [`usize`].
    pub const fn to_usize(self) -> usize {
        self as usize
    }
}

impl Default for CellSize {
    fn default() -> Self {
        Self::new()
    }
}

impl From<u8> for CellSize {
    fn from(val: u8) -> Self {
        Self::from_u8(val)
    }
}

impl From<u16> for CellSize {
    fn from(val: u16) -> Self {
        Self::from_u16(val)
    }
}

impl From<u32> for CellSize {
    fn from(val: u32) -> Self {
        Self::from_u32(val)
    }
}

impl From<u64> for CellSize {
    fn from(val: u64) -> Self {
        Self::from_u64(val)
    }
}

impl From<usize> for CellSize {
    fn from(val: usize) -> Self {
        Self::from_usize(val)
    }
}

impl From<CellSize> for u8 {
    fn from(val: CellSize) -> Self {
        val.to_u8() as Self
    }
}

impl From<CellSize> for u16 {
    fn from(val: CellSize) -> Self {
        val.to_u16()
    }
}

impl From<CellSize> for u32 {
    fn from(val: CellSize) -> Self {
        val.to_u32()
    }
}

impl From<CellSize> for u64 {
    fn from(val: CellSize) -> Self {
        val.to_u64()
    }
}

impl From<CellSize> for usize {
    fn from(val: CellSize) -> Self {
        val.to_usize()
    }
}
