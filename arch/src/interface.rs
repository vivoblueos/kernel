// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use core::ffi::c_void;

/// Architecture-local CPU identifier.
///
/// The value is meaningful to the selected architecture and board support
/// package. Kernel code should treat it as an index into per-CPU state after
/// board-level CPU topology has made that mapping valid.
pub type CpuId = usize;

/// Opaque interrupt state returned by [`ArchInterface::disable_local_irq_save`].
///
/// The exact bit layout is architecture-specific, for example BASEPRI on
/// Cortex-M, mstatus on RISC-V, or DAIF on AArch64. The kernel must only pass
/// this value back to [`ArchInterface::enable_local_irq_restore`].
pub type IrqState = usize;

/// Opaque context switch hook pointer.
///
/// This deliberately avoids exposing scheduler-owned kernel types through
/// `bluekernel_arch`. The compatibility facade in `kernel/src/arch` is
/// responsible for casting this pointer to the concrete kernel hook type while
/// the implementation is still being migrated.
pub type RawContextSwitchHook = *mut c_void;

/// Opaque architecture exception or trap frame pointer.
///
/// Architecture code owns the concrete frame layout. Kernel policy callbacks
/// may cast it back through the compatibility facade while migration is in
/// progress.
pub type RawExceptionFrame = *mut c_void;

/// Kernel-independent syscall request shape used by trap handlers.
#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct SyscallRequest {
    pub nr: usize,
    pub args: [usize; 6],
}

unsafe extern "C" {
    /// Notify kernel timekeeping that the architecture timer interrupt fired.
    ///
    /// Architecture code must only signal the event here. Claiming or clearing
    /// a board-specific timer interrupt remains kernel/board policy until the
    /// timer driver boundary is moved.
    pub fn blueos_kernel_handle_timer_tick();

    /// Dispatch a syscall request and return the raw syscall result.
    ///
    /// The request is intentionally a plain C-compatible value so trap code
    /// does not depend on kernel syscall context types.
    pub fn blueos_kernel_dispatch_syscall(req: *const SyscallRequest) -> usize;

    /// Enter and leave kernel IRQ accounting around an architecture trap.
    pub fn blueos_kernel_enter_irq() -> usize;
    pub fn blueos_kernel_leave_irq() -> usize;

    /// Return whether kernel scheduling policy wants to preempt after an IRQ.
    pub fn blueos_kernel_should_preempt_after_irq() -> bool;

    /// Complete a scheduler hook after architecture code saved a context.
    pub fn blueos_kernel_save_context_finish_hook(
        hook: RawContextSwitchHook,
        from_sp: usize,
    ) -> usize;

    /// Yield the current thread and return the next saved stack pointer.
    pub fn blueos_kernel_relinquish_me_and_return_next_sp(old_sp: usize) -> usize;

    /// Dispatch a board-owned external interrupt source.
    ///
    /// RISC-V PLIC/CLIC/INTC and AArch64 GIC policy can stay in board/kernel
    /// code while trap/vector entry moves into `bluekernel_arch`.
    pub fn blueos_kernel_dispatch_external_irq(
        frame: RawExceptionFrame,
        cause: usize,
        value: usize,
    ) -> usize;

    /// Report an unhandled architecture trap to the kernel fatal path.
    pub fn blueos_kernel_fatal_trap(frame: RawExceptionFrame, cause: usize, value: usize) -> !;

    /// Clear a software interrupt used as an inter-processor wakeup.
    pub fn blueos_kernel_clear_software_irq(cpu_id: usize);

    /// Finish the existing RISC-V ecall-based context switch path.
    ///
    /// Phase 3 moves the trap entry but Phase 4 still owns the thread context
    /// and scheduler switch ABI. This callback preserves the old ecall switch
    /// behavior without making `bluekernel_arch` depend on scheduler types.
    pub fn blueos_kernel_riscv_handle_ecall_switch(
        frame: RawExceptionFrame,
        cont: usize,
    ) -> usize;

    /// Apply RISC-V scheduler preemption policy after interrupt handling.
    ///
    /// The raw frame uses the same layout as the kernel-side RISC-V `Context`
    /// until Phase 4 moves context ownership into `bluekernel_arch`.
    pub fn blueos_kernel_riscv_might_switch_context(
        frame: RawExceptionFrame,
        cont: usize,
    ) -> usize;
}

/// Scheduler entry used when architecture code starts the first thread.
///
/// The entry never returns. Existing architecture facades may expose
/// `start_schedule` as a function returning `()`, because the non-returning
/// behavior is enforced inside the architecture assembly path.
pub type ScheduleEntry = extern "C" fn() -> !;

/// Continuation invoked after switching to another stack.
///
/// The first argument is the new stack pointer and the second argument is the
/// old stack pointer captured by the architecture implementation.
pub type StackSwitchContinuation = extern "C" fn(sp: usize, old_sp: usize);

/// Common shape required from an architecture thread context.
///
/// Register layout, stack frame details, and privilege-state bits remain
/// private to each architecture. The kernel only needs these operations to
/// build initial thread and signal contexts without knowing those details.
pub trait ThreadContext {
    /// Initialize architecture-required default context state.
    fn init(&mut self) -> &mut Self;

    /// Set the address where execution resumes when this context is restored.
    fn set_return_address(&mut self, address: usize) -> &mut Self;

    /// Set a C-ABI argument register by index.
    ///
    /// Unsupported indexes may be ignored or rejected by the architecture
    /// implementation. Stack-passed arguments are outside this minimal
    /// contract for now.
    fn set_arg(&mut self, index: usize, value: usize) -> &mut Self;
}

/// Kernel-independent architecture contract.
///
/// This trait describes the boundary that `bluekernel_arch` should eventually
/// implement directly. During the extraction, `kernel/src/arch` implements it
/// as a compatibility facade over the existing target-specific modules. The
/// trait must stay free of kernel crate types to avoid dependency cycles.
pub trait ArchInterface {
    /// Saved thread context type for the selected architecture.
    type Context: ThreadContext;

    /// Interrupt or exception frame type exposed to kernel fault paths.
    type IsrContext;

    /// Disable local interrupts on the current CPU.
    fn disable_local_irq();

    /// Enable local interrupts on the current CPU.
    fn enable_local_irq();

    /// Disable local interrupts and return the previous interrupt state.
    fn disable_local_irq_save() -> IrqState;

    /// Restore a state returned by [`Self::disable_local_irq_save`].
    fn enable_local_irq_restore(old: IrqState);

    /// Return whether local interrupts are currently enabled.
    fn local_irq_enabled() -> bool;

    /// Return the current architecture-local CPU identifier.
    fn current_cpu_id() -> CpuId;

    /// Return the current stack pointer.
    fn current_sp() -> usize;

    /// Enter the architecture's low-power idle instruction or idle loop.
    fn idle();

    /// Start scheduler execution from architecture boot or secondary CPU setup.
    fn start_schedule(cont: ScheduleEntry);

    /// Request a deferred context switch.
    fn pend_switch_context();

    /// Switch context and run scheduler-owned hooks through an opaque pointer.
    fn switch_context_with_hook(hook: RawContextSwitchHook);

    /// Restore another context and never return to the caller.
    fn restore_context_with_hook(hook: RawContextSwitchHook) -> !;

    /// Switch to `to_sp` and tail-call `cont`.
    fn switch_stack(to_sp: usize, cont: StackSwitchContinuation) -> !;
}
