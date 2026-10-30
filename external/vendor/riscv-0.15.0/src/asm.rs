//! Assembly instructions

macro_rules! instruction {
    ($(#[$attr:meta])*, unsafe $fnname:ident, $asm:expr, $($options:tt)*) => (
        $(#[$attr])*
        #[inline(always)]
        pub unsafe fn $fnname() {
            #[cfg(any(target_arch = "riscv32", target_arch = "riscv64"))]
            core::arch::asm!($asm, $($options)*);
            #[cfg(not(any(target_arch = "riscv32", target_arch = "riscv64")))]
            unimplemented!();
        }
    );
    ($(#[$attr:meta])*, $fnname:ident, $asm:expr, $($options:tt)*) => (
        $(#[$attr])*
        #[inline(always)]
        pub fn $fnname() {
            #[cfg(any(target_arch = "riscv32", target_arch = "riscv64"))]
            unsafe { core::arch::asm!($asm, $($options)*) };
            #[cfg(not(any(target_arch = "riscv32", target_arch = "riscv64")))]
            unimplemented!();
        }
    );
}

instruction!(
    /// `nop` instruction wrapper
    ///
    /// The `NOP` instruction does not change any architecturally visible state, except for
    /// advancing the pc and incrementing any applicable performance counters.
    ///
    /// This function generates a no-operation; it's useful to prevent delay loops from being
    /// optimized away.
    , nop, "nop", options(nomem, nostack));

instruction!(
    /// `WFI` instruction wrapper
    ///
    /// Provides a hint to the implementation that the current hart can be stalled until an interrupt might need servicing.
    /// The WFI instruction is just a hint, and a legal implementation is to implement WFI as a NOP.
    , wfi, "wfi", options(nomem, nostack));

instruction!(
    /// `EBREAK` instruction wrapper
    ///
    /// Generates a breakpoint exception.
    , unsafe ebreak, "ebreak", options(nomem, nostack));

instruction!(
    /// `ECALL` instruction wrapper
    ///
    /// Generates an exception for a service request to the execution environment.
    /// When executed in U-mode, S-mode, or M-mode, it generates an environment-call-from-U-mode
    /// exception, environment-call-from-S-mode exception, or environment-call-from-M-mode exception,
    /// respectively, and performs no other operation.
    ///
    /// # Note
    ///
    /// The ECALL instruction will **NOT** save and restore the stack pointer, as it triggers an exception.
    /// The stack pointer must be saved and restored accordingly by the exception handler.
    , unsafe ecall, "ecall", options(nomem, nostack));

instruction!(
    /// `SFENCE.VMA` instruction wrapper (all address spaces and page table levels)
    ///
    /// Synchronizes updates to in-memory memory-management data structures with current execution.
    /// Instruction execution causes implicit reads and writes to these data structures; however, these implicit references
    /// are ordinarily not ordered with respect to loads and stores in the instruction stream.
    /// Executing an `SFENCE.VMA` instruction guarantees that any stores in the instruction stream prior to the
    /// `SFENCE.VMA` are ordered before all implicit references subsequent to the `SFENCE.VMA`.
    , sfence_vma_all, "sfence.vma", options(nostack));

instruction!(
    /// `FENCE` instruction wrapper
    ///
    /// The FENCE instruction is used to order device I/O and memory accesses as viewed by other RISC-V
    /// harts and external devices or coprocessors. Any combination of device input (I), device output
    /// (O), memory reads (R), and memory writes (W) may be ordered with respect to any combination
    /// of the same. Informally, no other RISC-V hart or external device can observe any operation in the
    /// successor set following a FENCE before any operation in the predecessor set preceding the FENCE.
    ///
    /// The FENCE instruction also orders memory reads and writes made by the hart as observed by
    /// memory reads and writes made by an external device. However, FENCE does not order observations
    /// of events made by an external device using any other signaling mechanism.
    , fence, "fence", options(nostack));

instruction!(
    /// `FENCE.I` instruction wrapper
    ///
    /// Used to synchronize the instruction and data streams. RISC-V does not guarantee that
    /// stores to instruction memory will be made visible to instruction fetches on a
    /// RISC-V hart until that hart executes a FENCE.I instruction.
    ///
    /// A FENCE.I instruction ensures that a subsequent instruction fetch on a RISC-V hart
    /// will see any previous data stores already visible to the same RISC-V hart.
    /// FENCE.I does not ensure that other RISC-V harts’ instruction fetches will observe the
    /// local hart’s stores in a multiprocessor system. To make a store to instruction memory
    /// visible to all RISC-V harts, the writing hart also has to execute a data FENCE before
    /// requesting that all remote RISC-V harts execute a FENCE.I.
    ///
    /// The unused fields in the FENCE.I instruction, imm\[11:0\], rs1, and rd, are reserved for
    /// finer-grain fences in future extensions. For forward compatibility, base
    /// implementations shall ignore these fields, and standard software shall zero these fields.
    , fence_i, "fence.i", options(nostack));

/// `SFENCE.VMA` instruction wrapper
///
/// Synchronizes updates to in-memory memory-management data structures with current execution.
/// Instruction execution causes implicit reads and writes to these data structures; however, these implicit references
/// are ordinarily not ordered with respect to loads and stores in the instruction stream.
/// Executing an `SFENCE.VMA` instruction guarantees that any stores in the instruction stream prior to the
/// `SFENCE.VMA` are ordered before all implicit references subsequent to the `SFENCE.VMA`.
#[inline(always)]
#[cfg_attr(
    not(any(target_arch = "riscv32", target_arch = "riscv64")),
    allow(unused_variables)
)]
pub fn sfence_vma(asid: usize, addr: usize) {
    #[cfg(any(target_arch = "riscv32", target_arch = "riscv64"))]
    unsafe {
        core::arch::asm!("sfence.vma {0}, {1}", in(reg) addr, in(reg) asid, options(nostack));
    };
    #[cfg(not(any(target_arch = "riscv32", target_arch = "riscv64")))]
    unimplemented!();
}

/// Blocks the program for *at least* `cycles` CPU cycles.
///
/// This is implemented in assembly so its execution time is independent of the optimization
/// level, however it is dependent on the specific architecture and core configuration.
///
/// NOTE that the delay can take much longer if interrupts are serviced during its execution
/// and the execution time may vary with other factors. This delay is mainly useful for simple
/// timer-less initialization of peripherals if and only if accurate timing is not essential. In
/// any other case please use a more accurate method to produce a delay.
#[inline]
#[cfg_attr(
    not(any(target_arch = "riscv32", target_arch = "riscv64")),
    allow(unused_variables)
)]
pub fn delay(cycles: u32) {
    match () {
        #[cfg(any(target_arch = "riscv32", target_arch = "riscv64"))]
        () => {
            let real_cyc = 1 + cycles / 2;
            unsafe {
                core::arch::asm!(
                "2:",
                "addi {0}, {0}, -1",
                "bne {0}, zero, 2b",
                inout(reg) real_cyc => _,
                options(nomem, nostack),
                );
            }
        }
        #[cfg(not(any(target_arch = "riscv32", target_arch = "riscv64")))]
        () => unimplemented!(),
    }
}
