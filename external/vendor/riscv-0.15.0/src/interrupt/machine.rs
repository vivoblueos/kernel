use crate::{
    interrupt::Trap,
    register::{mcause, mepc, mie, mip, mstatus},
};
use riscv_pac::{
    result::{Error, Result},
    CoreInterruptNumber, ExceptionNumber, InterruptNumber,
};

/// Standard M-mode RISC-V interrupts
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(usize)]
pub enum Interrupt {
    SupervisorSoft = 1,
    MachineSoft = 3,
    SupervisorTimer = 5,
    MachineTimer = 7,
    SupervisorExternal = 9,
    MachineExternal = 11,
}

/// SAFETY: `Interrupt` represents the standard RISC-V interrupts
unsafe impl InterruptNumber for Interrupt {
    const MAX_INTERRUPT_NUMBER: usize = Self::MachineExternal as usize;

    #[inline]
    fn number(self) -> usize {
        self as usize
    }

    #[inline]
    fn from_number(value: usize) -> Result<Self> {
        match value {
            1 => Ok(Self::SupervisorSoft),
            3 => Ok(Self::MachineSoft),
            5 => Ok(Self::SupervisorTimer),
            7 => Ok(Self::MachineTimer),
            9 => Ok(Self::SupervisorExternal),
            11 => Ok(Self::MachineExternal),
            _ => Err(Error::InvalidVariant(value)),
        }
    }
}

/// SAFETY: `Interrupt` represents the standard RISC-V core interrupts
unsafe impl CoreInterruptNumber for Interrupt {}

/// Standard M-mode RISC-V exceptions
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(usize)]
pub enum Exception {
    InstructionMisaligned = 0,
    InstructionFault = 1,
    IllegalInstruction = 2,
    Breakpoint = 3,
    LoadMisaligned = 4,
    LoadFault = 5,
    StoreMisaligned = 6,
    StoreFault = 7,
    UserEnvCall = 8,
    SupervisorEnvCall = 9,
    MachineEnvCall = 11,
    InstructionPageFault = 12,
    LoadPageFault = 13,
    StorePageFault = 15,
}

/// SAFETY: `Exception` represents the standard RISC-V exceptions
unsafe impl ExceptionNumber for Exception {
    const MAX_EXCEPTION_NUMBER: usize = Self::StorePageFault as usize;

    #[inline]
    fn number(self) -> usize {
        self as usize
    }

    #[inline]
    fn from_number(value: usize) -> Result<Self> {
        match value {
            0 => Ok(Self::InstructionMisaligned),
            1 => Ok(Self::InstructionFault),
            2 => Ok(Self::IllegalInstruction),
            3 => Ok(Self::Breakpoint),
            4 => Ok(Self::LoadMisaligned),
            5 => Ok(Self::LoadFault),
            6 => Ok(Self::StoreMisaligned),
            7 => Ok(Self::StoreFault),
            8 => Ok(Self::UserEnvCall),
            9 => Ok(Self::SupervisorEnvCall),
            11 => Ok(Self::MachineEnvCall),
            12 => Ok(Self::InstructionPageFault),
            13 => Ok(Self::LoadPageFault),
            15 => Ok(Self::StorePageFault),
            _ => Err(Error::InvalidVariant(value)),
        }
    }
}

/// Checks if a specific core interrupt source is enabled in the current hart (machine mode).
#[inline]
pub fn is_interrupt_enabled<I: CoreInterruptNumber>(interrupt: I) -> bool {
    mie::read().is_enabled(interrupt)
}

/// Disables interrupts for a specific core interrupt source in the current hart (machine mode).
#[inline]
pub fn disable_interrupt<I: CoreInterruptNumber>(interrupt: I) {
    mie::disable(interrupt);
}

/// Enables interrupts for a specific core interrupt source in the current hart (machine mode).
///
/// # Note
///
/// Interrupts will only be triggered if globally enabled in the hart. To do this, use [`enable`].
///
/// # Safety
///
/// Enabling interrupts might break critical sections or other synchronization mechanisms.
/// Ensure that this is called in a safe context where interrupts can be enabled.
#[inline]
pub unsafe fn enable_interrupt<I: CoreInterruptNumber>(interrupt: I) {
    mie::enable(interrupt);
}

/// Checks if a specific core interrupt source is pending in the current hart (machine mode).
#[inline]
pub fn is_interrupt_pending<I: CoreInterruptNumber>(interrupt: I) -> bool {
    mip::read().is_pending(interrupt)
}

/// Disables interrupts globally in the current hart (machine mode).
#[inline]
pub fn disable() {
    // SAFETY: It is safe to disable interrupts
    unsafe { mstatus::clear_mie() }
}

/// Enables interrupts globally in the current hart (machine mode).
///
/// # Note
///
/// Only enabled interrupt sources will be triggered.
/// To enable specific interrupt sources, use [`enable_interrupt`].
///
/// # Safety
///
/// Enabling interrupts might break critical sections or other synchronization mechanisms.
/// Ensure that this is called in a safe context where interrupts can be enabled.
#[inline]
pub unsafe fn enable() {
    mstatus::set_mie()
}

/// Retrieves the cause of a trap in the current hart (machine mode).
///
/// This function expects the target-specific interrupt and exception types.
/// If the raw cause is not a valid interrupt or exception for the target, it returns an error.
#[inline]
pub fn try_cause<I: CoreInterruptNumber, E: ExceptionNumber>() -> Result<Trap<I, E>> {
    mcause::read().cause().try_into()
}

/// Retrieves the cause of a trap in the current hart (machine mode).
///
/// This function expects the target-specific interrupt and exception types.
/// If the raw cause is not a valid interrupt or exception for the target, it panics.
#[inline]
pub fn cause<I: CoreInterruptNumber, E: ExceptionNumber>() -> Trap<I, E> {
    try_cause().unwrap()
}

/// Execute closure `f` with interrupts disabled in the current hart (machine mode).
///
/// This method does not synchronise multiple harts, so it is not suitable for
/// using as a critical section. See the `critical-section` crate for a cross-platform
/// way to enter a critical section which provides a `CriticalSection` token.
///
/// This crate provides an implementation for `critical-section` suitable for single-hart systems,
/// based on disabling all interrupts. It can be enabled with the `critical-section-single-hart` feature.
#[inline]
pub fn free<F, R>(f: F) -> R
where
    F: FnOnce() -> R,
{
    let mstatus = mstatus::read();

    // disable interrupts
    disable();

    let r = f();

    // If the interrupts were active before our `disable` call, then re-enable
    // them. Otherwise, keep them disabled
    if mstatus.mie() {
        unsafe { enable() };
    }

    r
}

/// Execute closure `f` with interrupts enabled in the current hart (machine mode).
///
/// This method is assumed to be called within an interrupt handler, and allows
/// nested interrupts to occur. After the closure `f` is executed, the [`mstatus`]
/// and [`mepc`] registers are properly restored to their previous values.
///
/// # Safety
///
/// - Do not call this function inside a critical section.
/// - This method is assumed to be called within an interrupt handler.
/// - Make sure to clear the interrupt flag that caused the interrupt before calling
///   this method. Otherwise, the interrupt will be re-triggered before executing `f`.
#[inline]
pub unsafe fn nested<F, R>(f: F) -> R
where
    F: FnOnce() -> R,
{
    let mstatus = mstatus::read();
    let mepc = mepc::read();

    // enable interrupts to allow nested interrupts
    enable();

    let r = f();

    // If the interrupts were inactive before our `enable` call, then re-disable
    // them. Otherwise, keep them enabled
    if !mstatus.mie() {
        disable();
    }

    // Restore MSTATUS.PIE, MSTATUS.MPP, and SEPC
    if mstatus.mpie() {
        mstatus::set_mpie();
    }
    mstatus::set_mpp(mstatus.mpp());
    mepc::write(mepc);

    r
}

#[cfg(test)]
mod test {
    use super::*;
    use Exception::*;
    use Interrupt::*;

    #[test]
    fn test_interrupt() {
        assert_eq!(Interrupt::from_number(1), Ok(SupervisorSoft));
        assert_eq!(Interrupt::from_number(2), Err(Error::InvalidVariant(2)));
        assert_eq!(Interrupt::from_number(3), Ok(MachineSoft));
        assert_eq!(Interrupt::from_number(4), Err(Error::InvalidVariant(4)));
        assert_eq!(Interrupt::from_number(5), Ok(SupervisorTimer));
        assert_eq!(Interrupt::from_number(6), Err(Error::InvalidVariant(6)));
        assert_eq!(Interrupt::from_number(7), Ok(MachineTimer));
        assert_eq!(Interrupt::from_number(8), Err(Error::InvalidVariant(8)));
        assert_eq!(Interrupt::from_number(9), Ok(SupervisorExternal));
        assert_eq!(Interrupt::from_number(10), Err(Error::InvalidVariant(10)));
        assert_eq!(Interrupt::from_number(11), Ok(MachineExternal));
        assert_eq!(Interrupt::from_number(12), Err(Error::InvalidVariant(12)));

        assert_eq!(SupervisorSoft.number(), 1);
        assert_eq!(MachineSoft.number(), 3);
        assert_eq!(SupervisorTimer.number(), 5);
        assert_eq!(MachineTimer.number(), 7);
        assert_eq!(SupervisorExternal.number(), 9);
        assert_eq!(MachineExternal.number(), 11);

        assert_eq!(MachineExternal.number(), Interrupt::MAX_INTERRUPT_NUMBER)
    }

    #[test]
    fn test_exception() {
        assert_eq!(Exception::from_number(0), Ok(InstructionMisaligned));
        assert_eq!(Exception::from_number(1), Ok(InstructionFault));
        assert_eq!(Exception::from_number(2), Ok(IllegalInstruction));
        assert_eq!(Exception::from_number(3), Ok(Breakpoint));
        assert_eq!(Exception::from_number(4), Ok(LoadMisaligned));
        assert_eq!(Exception::from_number(5), Ok(LoadFault));
        assert_eq!(Exception::from_number(6), Ok(StoreMisaligned));
        assert_eq!(Exception::from_number(7), Ok(StoreFault));
        assert_eq!(Exception::from_number(8), Ok(UserEnvCall));
        assert_eq!(Exception::from_number(9), Ok(SupervisorEnvCall));
        assert_eq!(Exception::from_number(10), Err(Error::InvalidVariant(10)));
        assert_eq!(Exception::from_number(11), Ok(MachineEnvCall));
        assert_eq!(Exception::from_number(12), Ok(InstructionPageFault));
        assert_eq!(Exception::from_number(13), Ok(LoadPageFault));
        assert_eq!(Exception::from_number(14), Err(Error::InvalidVariant(14)));
        assert_eq!(Exception::from_number(15), Ok(StorePageFault));
        assert_eq!(Exception::from_number(16), Err(Error::InvalidVariant(16)));

        assert_eq!(InstructionMisaligned.number(), 0);
        assert_eq!(InstructionFault.number(), 1);
        assert_eq!(IllegalInstruction.number(), 2);
        assert_eq!(Breakpoint.number(), 3);
        assert_eq!(LoadMisaligned.number(), 4);
        assert_eq!(LoadFault.number(), 5);
        assert_eq!(StoreMisaligned.number(), 6);
        assert_eq!(StoreFault.number(), 7);
        assert_eq!(UserEnvCall.number(), 8);
        assert_eq!(SupervisorEnvCall.number(), 9);
        assert_eq!(MachineEnvCall.number(), 11);
        assert_eq!(InstructionPageFault.number(), 12);
        assert_eq!(LoadPageFault.number(), 13);
        assert_eq!(StorePageFault.number(), 15);

        assert_eq!(StorePageFault.number(), Exception::MAX_EXCEPTION_NUMBER)
    }
}
