//! Implementation Control Block

#[cfg(any(armv7m, armv8m, native))]
use volatile_register::RO;
use volatile_register::RW;

/// Register block
#[repr(C)]
pub struct RegisterBlock {
    /// Interrupt Controller Type Register
    ///
    /// The bottom four bits of this register give the number of implemented
    /// interrupt lines, divided by 32. So a value of `0b0010` indicates 64
    /// interrupts.
    #[cfg(any(armv7m, armv8m, native))]
    pub ictr: RO<u32>,

    /// The ICTR is not defined in the ARMv6-M Architecture Reference manual, so
    /// we replace it with this.
    #[cfg(not(any(armv7m, armv8m, native)))]
    _reserved: u32,

    /// Auxiliary Control Register
    ///
    /// This register is entirely implementation defined -- the standard gives
    /// it an address, but does not define its role or contents.
    pub actlr: RW<u32>,

    /// Coprocessor Power Control Register
    #[cfg(armv8m)]
    pub cppwr: RW<u32>,
}
