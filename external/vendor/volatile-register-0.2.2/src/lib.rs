//! Volatile access to memory mapped hardware registers
//!
//! # Usage
//!
//! ``` no_run
//! use volatile_register::RW;
//!
//! // Create a struct that represents the memory mapped register block
//! /// Nested Vector Interrupt Controller
//! #[repr(C)]
//! pub struct Nvic {
//!     /// Interrupt Set-Enable
//!     pub iser: [RW<u32>; 8],
//!     reserved0: [u32; 24],
//!     /// Interrupt Clear-Enable
//!     pub icer: [RW<u32>; 8],
//!     reserved1: [u32; 24],
//!     // .. more registers ..
//! }
//!
//! // Access the registers by casting the base address of the register block
//! // to the previously declared `struct`
//! let nvic = 0xE000_E100 as *const Nvic;
//! // Unsafe because the compiler can't verify the address is correct
//! unsafe { (*nvic).iser[0].write(1) }
//! ```

#![deny(missing_docs)]
#![no_std]

extern crate vcell;

use vcell::VolatileCell;

/// Read-Only register
#[repr(transparent)]
pub struct RO<T>
    where T: Copy
{
    register: VolatileCell<T>,
}

impl<T> RO<T>
    where T: Copy
{
    /// Reads the value of the register
    #[inline(always)]
    pub fn read(&self) -> T {
        self.register.get()
    }
}

/// Read-Write register
#[repr(transparent)]
pub struct RW<T>
    where T: Copy
{
    register: VolatileCell<T>,
}

impl<T> RW<T>
    where T: Copy
{
    /// Performs a read-modify-write operation
    ///
    /// NOTE: `unsafe` because writes to a register are side effectful
    #[inline(always)]
    pub unsafe fn modify<F>(&self, f: F)
        where F: FnOnce(T) -> T
    {
        self.register.set(f(self.register.get()));
    }

    /// Reads the value of the register
    #[inline(always)]
    pub fn read(&self) -> T {
        self.register.get()
    }

    /// Writes a `value` into the register
    ///
    /// NOTE: `unsafe` because writes to a register are side effectful
    #[inline(always)]
    pub unsafe fn write(&self, value: T) {
        self.register.set(value)
    }
}

/// Write-Only register
#[repr(transparent)]
pub struct WO<T>
    where T: Copy
{
    register: VolatileCell<T>,
}

impl<T> WO<T>
    where T: Copy
{
    /// Writes `value` into the register
    ///
    /// NOTE: `unsafe` because writes to a register are side effectful
    #[inline(always)]
    pub unsafe fn write(&self, value: T) {
        self.register.set(value)
    }
}
