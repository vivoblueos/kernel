//! Nested Vector Interrupt Controller

use volatile_register::RW;
#[cfg(not(armv6m))]
use volatile_register::{RO, WO};

use crate::interrupt::InterruptNumber;
use crate::peripheral::NVIC;

/// Register block
#[repr(C)]
pub struct RegisterBlock {
    /// Interrupt Set-Enable
    pub iser: [RW<u32>; 16],

    _reserved0: [u32; 16],

    /// Interrupt Clear-Enable
    pub icer: [RW<u32>; 16],

    _reserved1: [u32; 16],

    /// Interrupt Set-Pending
    pub ispr: [RW<u32>; 16],

    _reserved2: [u32; 16],

    /// Interrupt Clear-Pending
    pub icpr: [RW<u32>; 16],

    _reserved3: [u32; 16],

    /// Interrupt Active Bit (not present on Cortex-M0 variants)
    #[cfg(not(armv6m))]
    pub iabr: [RO<u32>; 16],
    #[cfg(armv6m)]
    _reserved4: [u32; 16],

    _reserved5: [u32; 48],

    /// Interrupt Priority
    ///
    /// On ARMv7-M, 124 word-sized registers are available. Each of those
    /// contains of 4 interrupt priorities of 8 byte each.The architecture
    /// specifically allows accessing those along byte boundaries, so they are
    /// represented as 496 byte-sized registers, for convenience, and to allow
    /// atomic priority updates.
    ///
    /// On ARMv6-M, the registers must only be accessed along word boundaries,
    /// so convenient byte-sized representation wouldn't work on that
    /// architecture.
    #[cfg(not(armv6m))]
    pub ipr: [RW<u8>; 496],

    /// Interrupt Priority
    ///
    /// On ARMv7-M, 124 word-sized registers are available. Each of those
    /// contains of 4 interrupt priorities of 8 byte each.The architecture
    /// specifically allows accessing those along byte boundaries, so they are
    /// represented as 496 byte-sized registers, for convenience, and to allow
    /// atomic priority updates.
    ///
    /// On ARMv6-M, the registers must only be accessed along word boundaries,
    /// so convenient byte-sized representation wouldn't work on that
    /// architecture.
    #[cfg(armv6m)]
    pub ipr: [RW<u32>; 8],

    #[cfg(not(armv6m))]
    _reserved6: [u32; 580],

    /// Software Trigger Interrupt
    #[cfg(not(armv6m))]
    pub stir: WO<u32>,
}

impl NVIC {
    /// Request an IRQ in software
    ///
    /// Writing a value to the INTID field is the same as manually pending an interrupt by setting
    /// the corresponding interrupt bit in an Interrupt Set Pending Register. This is similar to
    /// [`NVIC::pend`].
    ///
    /// This method is not available on ARMv6-M chips.
    ///
    /// [`NVIC::pend`]: #method.pend
    #[cfg(not(armv6m))]
    #[inline]
    pub fn request<I>(&mut self, interrupt: I)
    where
        I: InterruptNumber,
    {
        let nr = interrupt.number();

        unsafe {
            self.stir.write(u32::from(nr));
        }
    }

    /// Disables `interrupt`
    #[inline]
    pub fn mask<I>(interrupt: I)
    where
        I: InterruptNumber,
    {
        let nr = interrupt.number();
        // NOTE(unsafe) this is a write to a stateless register
        unsafe { (*Self::PTR).icer[usize::from(nr / 32)].write(1 << (nr % 32)) }
    }

    /// Enables `interrupt`
    ///
    /// This function is `unsafe` because it can break mask-based critical sections
    #[inline]
    pub unsafe fn unmask<I>(interrupt: I)
    where
        I: InterruptNumber,
    {
        let nr = interrupt.number();
        // NOTE(ptr) this is a write to a stateless register
        (*Self::PTR).iser[usize::from(nr / 32)].write(1 << (nr % 32))
    }

    /// Returns the NVIC priority of `interrupt`
    ///
    /// *NOTE* NVIC encodes priority in the highest bits of a byte so values like `1` and `2` map
    /// to the same priority. Also for NVIC priorities, a lower value (e.g. `16`) has higher
    /// priority (urgency) than a larger value (e.g. `32`).
    #[inline]
    pub fn get_priority<I>(interrupt: I) -> u8
    where
        I: InterruptNumber,
    {
        #[cfg(not(armv6m))]
        {
            let nr = interrupt.number();
            // NOTE(unsafe) atomic read with no side effects
            unsafe { (*Self::PTR).ipr[usize::from(nr)].read() }
        }

        #[cfg(armv6m)]
        {
            // NOTE(unsafe) atomic read with no side effects
            let ipr_n = unsafe { (*Self::PTR).ipr[Self::ipr_index(interrupt)].read() };
            let prio = (ipr_n >> Self::ipr_shift(interrupt)) & 0x0000_00ff;
            prio as u8
        }
    }

    /// Is `interrupt` active or pre-empted and stacked
    #[cfg(not(armv6m))]
    #[inline]
    pub fn is_active<I>(interrupt: I) -> bool
    where
        I: InterruptNumber,
    {
        let nr = interrupt.number();
        let mask = 1 << (nr % 32);

        // NOTE(unsafe) atomic read with no side effects
        unsafe { ((*Self::PTR).iabr[usize::from(nr / 32)].read() & mask) == mask }
    }

    /// Checks if `interrupt` is enabled
    #[inline]
    pub fn is_enabled<I>(interrupt: I) -> bool
    where
        I: InterruptNumber,
    {
        let nr = interrupt.number();
        let mask = 1 << (nr % 32);

        // NOTE(unsafe) atomic read with no side effects
        unsafe { ((*Self::PTR).iser[usize::from(nr / 32)].read() & mask) == mask }
    }

    /// Checks if `interrupt` is pending
    #[inline]
    pub fn is_pending<I>(interrupt: I) -> bool
    where
        I: InterruptNumber,
    {
        let nr = interrupt.number();
        let mask = 1 << (nr % 32);

        // NOTE(unsafe) atomic read with no side effects
        unsafe { ((*Self::PTR).ispr[usize::from(nr / 32)].read() & mask) == mask }
    }

    /// Forces `interrupt` into pending state
    #[inline]
    pub fn pend<I>(interrupt: I)
    where
        I: InterruptNumber,
    {
        let nr = interrupt.number();

        // NOTE(unsafe) atomic stateless write; ICPR doesn't store any state
        unsafe { (*Self::PTR).ispr[usize::from(nr / 32)].write(1 << (nr % 32)) }
    }

    /// Sets the "priority" of `interrupt` to `prio`
    ///
    /// *NOTE* See [`get_priority`](struct.NVIC.html#method.get_priority) method for an explanation
    /// of how NVIC priorities work.
    ///
    /// On ARMv6-M, updating an interrupt priority requires a read-modify-write operation. On
    /// ARMv7-M, the operation is performed in a single atomic write operation.
    ///
    /// # Unsafety
    ///
    /// Changing priority levels can break priority-based critical sections (see
    /// [`register::basepri`](crate::register::basepri)) and compromise memory safety.
    #[inline]
    pub unsafe fn set_priority<I>(&mut self, interrupt: I, prio: u8)
    where
        I: InterruptNumber,
    {
        #[cfg(not(armv6m))]
        {
            let nr = interrupt.number();
            self.ipr[usize::from(nr)].write(prio)
        }

        #[cfg(armv6m)]
        {
            self.ipr[Self::ipr_index(interrupt)].modify(|value| {
                let mask = 0x0000_00ff << Self::ipr_shift(interrupt);
                let prio = u32::from(prio) << Self::ipr_shift(interrupt);

                (value & !mask) | prio
            })
        }
    }

    /// Clears `interrupt`'s pending state
    #[inline]
    pub fn unpend<I>(interrupt: I)
    where
        I: InterruptNumber,
    {
        let nr = interrupt.number();

        // NOTE(unsafe) atomic stateless write; ICPR doesn't store any state
        unsafe { (*Self::PTR).icpr[usize::from(nr / 32)].write(1 << (nr % 32)) }
    }

    #[cfg(armv6m)]
    #[inline]
    fn ipr_index<I>(interrupt: I) -> usize
    where
        I: InterruptNumber,
    {
        usize::from(interrupt.number()) / 4
    }

    #[cfg(armv6m)]
    #[inline]
    fn ipr_shift<I>(interrupt: I) -> usize
    where
        I: InterruptNumber,
    {
        (usize::from(interrupt.number()) % 4) * 8
    }
}
