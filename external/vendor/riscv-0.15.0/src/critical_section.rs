use critical_section::{set_impl, Impl, RawRestoreState};

use crate::interrupt;

struct SingleHartCriticalSection;
set_impl!(SingleHartCriticalSection);

unsafe impl Impl for SingleHartCriticalSection {
    #[cfg(not(feature = "s-mode"))]
    unsafe fn acquire() -> RawRestoreState {
        let mut mstatus: usize;
        core::arch::asm!("csrrci {}, mstatus, 0b1000", out(reg) mstatus);
        core::mem::transmute::<_, crate::register::mstatus::Mstatus>(mstatus).mie()
    }

    #[cfg(feature = "s-mode")]
    unsafe fn acquire() -> RawRestoreState {
        let mut sstatus: usize;
        core::arch::asm!("csrrci {}, sstatus, 0b0010", out(reg) sstatus);
        core::mem::transmute::<_, crate::register::sstatus::Sstatus>(sstatus).sie()
    }

    unsafe fn release(was_active: RawRestoreState) {
        // Only re-enable interrupts if they were enabled before the critical section.
        if was_active {
            interrupt::enable()
        }
    }
}
