//! scause register

pub use crate::interrupt::Trap;
pub use riscv_pac::{CoreInterruptNumber, ExceptionNumber, InterruptNumber}; // re-export useful riscv-pac traits

read_write_csr! {
    /// scause register
    Scause: 0x142,
    mask: usize::MAX,
}

#[cfg(target_arch = "riscv32")]
read_write_csr_field! {
    Scause,
    /// Returns the type of the trap:
    ///
    /// - `true`: an interrupt caused the trap
    /// - `false`: an exception caused the trap
    interrupt: 31,
}

#[cfg(not(target_arch = "riscv32"))]
read_write_csr_field! {
    Scause,
    /// Returns the type of the trap:
    ///
    /// - `true`: an interrupt caused the trap
    /// - `false`: an exception caused the trap
    interrupt: 63,
}

#[cfg(target_arch = "riscv32")]
read_write_csr_field! {
    Scause,
    /// Returns the code field
    code: [0:30],
}

#[cfg(not(target_arch = "riscv32"))]
read_write_csr_field! {
    Scause,
    /// Returns the code field
    code: [0:62],
}

impl Scause {
    /// Returns the trap cause represented by this register.
    ///
    /// # Note
    ///
    /// This method returns a **raw trap cause**, which means that values are represented as `usize`.
    /// To get a target-specific trap cause, use [`Trap::try_into`] with your target-specific S-Mode trap cause types.
    #[inline]
    pub fn cause(&self) -> Trap<usize, usize> {
        if self.is_interrupt() {
            Trap::Interrupt(self.code())
        } else {
            Trap::Exception(self.code())
        }
    }

    /// Is trap cause an interrupt.
    #[inline]
    pub fn is_interrupt(&self) -> bool {
        self.interrupt()
    }

    /// Is trap cause an exception.
    #[inline]
    pub fn is_exception(&self) -> bool {
        !self.interrupt()
    }
}

/// Set supervisor cause register to corresponding cause.
#[inline]
pub unsafe fn set<I: CoreInterruptNumber, E: ExceptionNumber>(cause: Trap<I, E>) {
    let bits = match cause {
        Trap::Interrupt(i) => {
            i.number() | (1 << (usize::BITS as usize - 1)) // interrupt bit is 1
        }
        Trap::Exception(e) => e.number(),
    };
    _write(bits);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_scause() {
        let new_code = 0;
        (1usize..=usize::BITS as usize)
            .map(|r| ((1u128 << r) - 1) as usize)
            .for_each(|raw| {
                let exp_interrupt = (raw >> (usize::BITS - 1)) != 0;
                let exp_code = raw & ((1usize << (usize::BITS - 1)) - 1);
                let exp_cause = if exp_interrupt {
                    Trap::Interrupt(exp_code)
                } else {
                    Trap::Exception(exp_code)
                };

                let mut scause = Scause::from_bits(raw);

                assert_eq!(scause.interrupt(), exp_interrupt);
                assert_eq!(scause.is_interrupt(), exp_interrupt);
                assert_eq!(scause.is_exception(), !exp_interrupt);

                assert_eq!(scause.code(), exp_code);
                assert_eq!(scause.cause(), exp_cause);

                scause.set_interrupt(!exp_interrupt);

                assert_eq!(scause.is_interrupt(), !exp_interrupt);
                assert_eq!(scause.is_exception(), exp_interrupt);

                scause.set_code(new_code);
                let new_cause = if scause.interrupt() {
                    Trap::Interrupt(new_code)
                } else {
                    Trap::Exception(new_code)
                };

                assert_eq!(scause.code(), new_code);
                assert_eq!(scause.cause(), new_cause);

                scause.set_code(exp_code);
                let exp_cause = if scause.interrupt() {
                    Trap::Interrupt(exp_code)
                } else {
                    Trap::Exception(exp_code)
                };

                assert_eq!(scause.code(), exp_code);
                assert_eq!(scause.cause(), exp_cause);
            });
    }
}
