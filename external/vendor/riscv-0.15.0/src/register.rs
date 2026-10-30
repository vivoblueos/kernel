//! RISC-V CSR's
//!
//! The following registers are not available on 64-bit implementations.
//!
//! - cycleh
//! - timeh
//! - instreth
//! - hpmcounter<3-31>h
//! - mcycleh
//! - minstreth
//! - mhpmcounter<3-31>h
//! - mstatush
//!
//! # On Floating-Point CSRs
//!
//! We are deliberately *not* providing instructions that could change the floating-point rounding
//! mode or exception behavior or read the accrued exceptions flags: `frcsr`, `fscsr`, `fsrm`,
//! `frflags`, `fsflags`.
//!
//! Rust makes no guarantees whatsoever about the contents of the accrued exceptions register: Rust
//! floating-point operations may or may not result in this register getting updated with exception
//! state, and the register can change between two invocations of this function even when no
//! floating-point operations appear in the source code (since floating-point operations appearing
//! earlier or later can be reordered).
//!
//! Modifying the rounding mode leads to **immediate Undefined Behavior**: Rust assumes that the
//! default rounding mode is always set and will optimize accordingly. This even applies when the
//! rounding mode is altered and later reset to its original value without any floating-point
//! operations appearing in the source code between those operations (since floating-point
//! operations appearing earlier or later can be reordered).
//!
//! If you need to perform some floating-point operations and check whether they raised an
//! exception, use a single inline assembly block for the entire sequence of operations.
//!
//! If you need to perform some floating-point operations under a different rounding mode, use a
//! single inline assembly block and make sure to restore the original rounding mode before the end
//! of the block.

#[macro_use]
mod macros;

// User Counter/Timers
pub mod cycle;
pub mod cycleh;
mod hpmcounterx;
pub use self::hpmcounterx::*;
pub mod instret;
pub mod instreth;
pub mod time;
pub mod timeh;

// Supervisor Trap Setup
pub mod scounteren;
pub mod sie;
pub mod sstatus;
pub mod stvec;

// Supervisor Trap Handling
pub mod scause;
pub mod scontext;
pub mod senvcfg;
pub mod sepc;
pub mod sip;
pub mod sscratch;
pub mod stval;

// Supervisor Protection and Translation
pub mod satp;

// Machine Information Registers
pub mod marchid;
pub mod mhartid;
pub mod mimpid;
pub mod mvendorid;

// Machine Trap Setup
pub mod mcounteren;
pub mod medeleg;
pub mod mideleg;
pub mod mie;
pub mod misa;
pub mod mstatus;
pub mod mstatush;
pub mod mtvec;

// Machine Trap Handling
pub mod mcause;
pub mod mepc;
pub mod mip;
pub mod mscratch;
pub mod mtinst;
pub mod mtval;
pub mod mtval2;

// Machine Protection and Translation
mod pmpcfgx;
pub use self::pmpcfgx::*;
mod pmpaddrx;
pub use self::pmpaddrx::*;

// Machine Counter/Timers
pub mod mcountinhibit;
pub mod mcycle;
pub mod mcycleh;
mod mhpmcounterx;
pub use self::mhpmcounterx::*;
pub mod minstret;
pub mod minstreth;

// Machine Counter Setup
mod mhpmeventx;
pub use self::mhpmeventx::*;

// Machine configuration
pub mod mconfigptr;
pub mod mseccfg;
#[cfg(any(test, target_arch = "riscv32"))]
pub mod mseccfgh;

#[cfg(test)]
mod tests;

// TODO: Debug/Trace Registers (shared with Debug Mode)

// TODO: Debug Mode Registers
