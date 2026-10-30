#[cfg(all(cortex_m, feature = "critical-section-single-core"))]
mod single_core_critical_section {
    use critical_section::{set_impl, Impl, RawRestoreState};

    use crate::interrupt;
    use crate::register::primask;

    struct SingleCoreCriticalSection;
    set_impl!(SingleCoreCriticalSection);

    unsafe impl Impl for SingleCoreCriticalSection {
        unsafe fn acquire() -> RawRestoreState {
            let was_active = primask::read().is_active();
            interrupt::disable();
            was_active
        }

        unsafe fn release(was_active: RawRestoreState) {
            // Only re-enable interrupts if they were enabled before the critical section.
            if was_active {
                interrupt::enable()
            }
        }
    }
}
