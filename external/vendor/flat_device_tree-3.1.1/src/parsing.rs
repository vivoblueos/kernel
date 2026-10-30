// This Source Code Form is subject to the terms of the Mozilla Public License,
// v. 2.0. If a copy of the MPL was not distributed with this file, You can
// obtain one at https://mozilla.org/MPL/2.0/.

#[derive(Debug, Clone, Copy)]
#[repr(transparent)]
pub struct BigEndianU32(u32);

impl BigEndianU32 {
    /// Creates a new [BigEndianU32].
    pub const fn new() -> Self {
        Self(0)
    }

    /// Gets the inner value of the [BigEndianU32].
    pub fn get(self) -> u32 {
        self.0
    }

    /// Attempts to convert a byte buffer into a [BigEndianU32].
    pub(crate) fn from_bytes(bytes: &[u8]) -> Option<Self> {
        Some(BigEndianU32(u32::from_be_bytes(bytes.get(..4)?.try_into().ok()?)))
    }
}

impl Default for BigEndianU32 {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, Copy)]
#[repr(transparent)]
pub struct BigEndianU64(u64);

impl BigEndianU64 {
    /// Creates a new [BigEndianU64].
    pub const fn new() -> Self {
        Self(0)
    }

    /// Gets the inner value of the [BigEndianU64].
    pub fn get(&self) -> u64 {
        self.0
    }

    /// Attempts to convert a byte buffer into a [BigEndianU64].
    pub(crate) fn from_bytes(bytes: &[u8]) -> Option<Self> {
        Some(BigEndianU64(u64::from_be_bytes(bytes.get(..8)?.try_into().ok()?)))
    }
}

impl Default for BigEndianU64 {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, Copy)]
pub struct FdtData<'a> {
    bytes: &'a [u8],
}

impl<'a> FdtData<'a> {
    pub fn new(bytes: &'a [u8]) -> Self {
        Self { bytes }
    }

    pub fn u32(&mut self) -> Option<BigEndianU32> {
        let ret = BigEndianU32::from_bytes(self.bytes)?;
        self.skip(4)?;

        Some(ret)
    }

    pub fn u64(&mut self) -> Option<BigEndianU64> {
        let ret = BigEndianU64::from_bytes(self.bytes)?;
        self.skip(8)?;

        Some(ret)
    }

    pub fn skip(&mut self, n_bytes: usize) -> Option<()> {
        self.bytes = self.bytes.get(n_bytes..)?;
        Some(())
    }

    pub fn remaining(&self) -> &'a [u8] {
        self.bytes
    }

    pub fn peek_u32(&self) -> Option<BigEndianU32> {
        Self::new(self.remaining()).u32()
    }

    pub fn is_empty(&self) -> bool {
        self.remaining().is_empty()
    }

    pub fn skip_nops(&mut self) {
        while let Some(crate::node::FDT_NOP) = self.peek_u32().map(|n| n.get()) {
            let _ = self.u32();
        }
    }

    pub fn take(&mut self, bytes: usize) -> Option<&'a [u8]> {
        if self.bytes.len() >= bytes {
            let ret = self.bytes.get(..bytes)?;
            self.skip(bytes);

            return Some(ret);
        }

        None
    }
}
