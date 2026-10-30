// Copyright 2025 The safe-mmio Authors.
// This project is dual-licensed under Apache 2.0 and MIT terms.
// See LICENSE-APACHE and LICENSE-MIT for details.

use core::{
    fmt::{self, Debug, Formatter},
    marker::PhantomData,
};

/// The physical instance of some device's MMIO space.
pub struct PhysicalInstance<T> {
    pa: usize,
    _phantom: PhantomData<T>,
}

impl<T> Debug for PhysicalInstance<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        f.debug_struct("PhysicalInstance")
            .field("pa", &self.pa)
            .field("size", &size_of::<T>())
            .finish()
    }
}

impl<T> PhysicalInstance<T> {
    /// # Safety
    ///
    /// This must refer to the physical address of a real set of device registers of type `T`, and
    /// there must only ever be a single `PhysicalInstance` created for those device registers.
    pub const unsafe fn new(pa: usize) -> Self {
        Self {
            pa,
            _phantom: PhantomData,
        }
    }

    /// Returns the physical base address of the device's registers.
    pub const fn pa(&self) -> usize {
        self.pa
    }
}
