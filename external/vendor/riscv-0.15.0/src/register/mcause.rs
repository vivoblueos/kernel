//! mcause register

pub use crate::interrupt::Trap;

read_only_csr! {
    /// `mcause` register
    Mcause: 0x342,
    mask: usize::MAX,
}

#[cfg(target_arch = "riscv32")]
read_only_csr_field! {
    Mcause,
    /// Returns the `code` field.
    code: [0:30],
}

#[cfg(not(target_arch = "riscv32"))]
read_only_csr_field! {
    Mcause,
    /// Returns the `code` field.
    code: [0:62],
}

#[cfg(target_arch = "riscv32")]
read_only_csr_field! {
    Mcause,
    /// Is the trap cause an interrupt.
    is_interrupt: 31,
}

#[cfg(not(target_arch = "riscv32"))]
read_only_csr_field! {
    Mcause,
    /// Is the trap cause an interrupt.
    is_interrupt: 63,
}

impl Mcause {
    /// Returns the trap cause represented by this register.
    ///
    /// # Note
    ///
    /// This method returns a **raw trap cause**, which means that values are represented as `usize`.
    /// To get a target-specific trap cause, use [`Trap::try_into`] with your target-specific M-Mode trap cause types.
    #[inline]
    pub fn cause(&self) -> Trap<usize, usize> {
        if self.is_interrupt() {
            Trap::Interrupt(self.code())
        } else {
            Trap::Exception(self.code())
        }
    }

    /// Is trap cause an exception.
    #[inline]
    pub fn is_exception(&self) -> bool {
        !self.is_interrupt()
    }
}
