//! System Control Block

use core::ptr;

use volatile_register::RW;

#[cfg(not(armv6m))]
use super::cpuid::CsselrCacheType;
#[cfg(not(armv6m))]
use super::CBP;
#[cfg(not(armv6m))]
use super::CPUID;
use super::SCB;
#[cfg(feature = "serde")]
use serde::{Deserialize, Serialize};

/// Register block
#[repr(C)]
pub struct RegisterBlock {
    /// Interrupt Control and State
    pub icsr: RW<u32>,

    /// Vector Table Offset (not present on Cortex-M0 variants)
    pub vtor: RW<u32>,

    /// Application Interrupt and Reset Control
    pub aircr: RW<u32>,

    /// System Control
    pub scr: RW<u32>,

    /// Configuration and Control
    pub ccr: RW<u32>,

    /// System Handler Priority (word accessible only on Cortex-M0 variants)
    ///
    /// On ARMv7-M, `shpr[0]` points to SHPR1
    ///
    /// On ARMv6-M, `shpr[0]` points to SHPR2
    #[cfg(not(armv6m))]
    pub shpr: [RW<u8>; 12],
    #[cfg(armv6m)]
    _reserved1: u32,
    /// System Handler Priority (word accessible only on Cortex-M0 variants)
    ///
    /// On ARMv7-M, `shpr[0]` points to SHPR1
    ///
    /// On ARMv6-M, `shpr[0]` points to SHPR2
    #[cfg(armv6m)]
    pub shpr: [RW<u32>; 2],

    /// System Handler Control and State
    pub shcsr: RW<u32>,

    /// Configurable Fault Status (not present on Cortex-M0 variants)
    #[cfg(not(armv6m))]
    pub cfsr: RW<u32>,
    #[cfg(armv6m)]
    _reserved2: u32,

    /// HardFault Status (not present on Cortex-M0 variants)
    #[cfg(not(armv6m))]
    pub hfsr: RW<u32>,
    #[cfg(armv6m)]
    _reserved3: u32,

    /// Debug Fault Status (not present on Cortex-M0 variants)
    #[cfg(not(armv6m))]
    pub dfsr: RW<u32>,
    #[cfg(armv6m)]
    _reserved4: u32,

    /// MemManage Fault Address (not present on Cortex-M0 variants)
    #[cfg(not(armv6m))]
    pub mmfar: RW<u32>,
    #[cfg(armv6m)]
    _reserved5: u32,

    /// BusFault Address (not present on Cortex-M0 variants)
    #[cfg(not(armv6m))]
    pub bfar: RW<u32>,
    #[cfg(armv6m)]
    _reserved6: u32,

    /// Auxiliary Fault Status (not present on Cortex-M0 variants)
    #[cfg(not(armv6m))]
    pub afsr: RW<u32>,
    #[cfg(armv6m)]
    _reserved7: u32,

    _reserved8: [u32; 18],

    /// Coprocessor Access Control (not present on Cortex-M0 variants)
    #[cfg(not(armv6m))]
    pub cpacr: RW<u32>,
    #[cfg(armv6m)]
    _reserved9: u32,
}

/// FPU access mode
#[cfg(has_fpu)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FpuAccessMode {
    /// FPU is not accessible
    Disabled,
    /// FPU is accessible in Privileged and User mode
    Enabled,
    /// FPU is accessible in Privileged mode only
    Privileged,
}

#[cfg(has_fpu)]
mod fpu_consts {
    pub const SCB_CPACR_FPU_MASK: u32 = 0b11_11 << 20;
    pub const SCB_CPACR_FPU_ENABLE: u32 = 0b01_01 << 20;
    pub const SCB_CPACR_FPU_USER: u32 = 0b10_10 << 20;
}

#[cfg(has_fpu)]
use self::fpu_consts::*;

#[cfg(has_fpu)]
impl SCB {
    /// Shorthand for `set_fpu_access_mode(FpuAccessMode::Disabled)`
    #[inline]
    pub fn disable_fpu(&mut self) {
        self.set_fpu_access_mode(FpuAccessMode::Disabled)
    }

    /// Shorthand for `set_fpu_access_mode(FpuAccessMode::Enabled)`
    #[inline]
    pub fn enable_fpu(&mut self) {
        self.set_fpu_access_mode(FpuAccessMode::Enabled)
    }

    /// Gets FPU access mode
    #[inline]
    pub fn fpu_access_mode() -> FpuAccessMode {
        // NOTE(unsafe) atomic read operation with no side effects
        let cpacr = unsafe { (*Self::PTR).cpacr.read() };

        if cpacr & SCB_CPACR_FPU_MASK == SCB_CPACR_FPU_ENABLE | SCB_CPACR_FPU_USER {
            FpuAccessMode::Enabled
        } else if cpacr & SCB_CPACR_FPU_MASK == SCB_CPACR_FPU_ENABLE {
            FpuAccessMode::Privileged
        } else {
            FpuAccessMode::Disabled
        }
    }

    /// Sets FPU access mode
    ///
    /// *IMPORTANT* Any function that runs fully or partly with the FPU disabled must *not* take any
    /// floating-point arguments or have any floating-point local variables. Because the compiler
    /// might inline such a function into a caller that does have floating-point arguments or
    /// variables, any such function must be also marked #[inline(never)].
    #[inline]
    pub fn set_fpu_access_mode(&mut self, mode: FpuAccessMode) {
        let mut cpacr = self.cpacr.read() & !SCB_CPACR_FPU_MASK;
        match mode {
            FpuAccessMode::Disabled => (),
            FpuAccessMode::Privileged => cpacr |= SCB_CPACR_FPU_ENABLE,
            FpuAccessMode::Enabled => cpacr |= SCB_CPACR_FPU_ENABLE | SCB_CPACR_FPU_USER,
        }
        unsafe { self.cpacr.write(cpacr) }
    }
}

impl SCB {
    /// Returns the active exception number
    #[inline]
    pub fn vect_active() -> VectActive {
        let icsr = unsafe { ptr::read(&(*SCB::PTR).icsr as *const _ as *const u32) };

        match icsr as u8 {
            0 => VectActive::ThreadMode,
            2 => VectActive::Exception(Exception::NonMaskableInt),
            3 => VectActive::Exception(Exception::HardFault),
            #[cfg(not(armv6m))]
            4 => VectActive::Exception(Exception::MemoryManagement),
            #[cfg(not(armv6m))]
            5 => VectActive::Exception(Exception::BusFault),
            #[cfg(not(armv6m))]
            6 => VectActive::Exception(Exception::UsageFault),
            #[cfg(any(armv8m, native))]
            7 => VectActive::Exception(Exception::SecureFault),
            11 => VectActive::Exception(Exception::SVCall),
            #[cfg(not(armv6m))]
            12 => VectActive::Exception(Exception::DebugMonitor),
            14 => VectActive::Exception(Exception::PendSV),
            15 => VectActive::Exception(Exception::SysTick),
            irqn => VectActive::Interrupt { irqn: irqn - 16 },
        }
    }
}

/// Processor core exceptions (internal interrupts)
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "std", derive(PartialOrd, Hash))]
pub enum Exception {
    /// Non maskable interrupt
    NonMaskableInt,

    /// Hard fault interrupt
    HardFault,

    /// Memory management interrupt (not present on Cortex-M0 variants)
    #[cfg(not(armv6m))]
    MemoryManagement,

    /// Bus fault interrupt (not present on Cortex-M0 variants)
    #[cfg(not(armv6m))]
    BusFault,

    /// Usage fault interrupt (not present on Cortex-M0 variants)
    #[cfg(not(armv6m))]
    UsageFault,

    /// Secure fault interrupt (only on ARMv8-M)
    #[cfg(any(armv8m, native))]
    SecureFault,

    /// SV call interrupt
    SVCall,

    /// Debug monitor interrupt (not present on Cortex-M0 variants)
    #[cfg(not(armv6m))]
    DebugMonitor,

    /// Pend SV interrupt
    PendSV,

    /// System Tick interrupt
    SysTick,
}

impl Exception {
    /// Returns the IRQ number of this `Exception`
    ///
    /// The return value is always within the closed range `[-1, -14]`
    #[inline]
    pub fn irqn(self) -> i8 {
        match self {
            Exception::NonMaskableInt => -14,
            Exception::HardFault => -13,
            #[cfg(not(armv6m))]
            Exception::MemoryManagement => -12,
            #[cfg(not(armv6m))]
            Exception::BusFault => -11,
            #[cfg(not(armv6m))]
            Exception::UsageFault => -10,
            #[cfg(any(armv8m, native))]
            Exception::SecureFault => -9,
            Exception::SVCall => -5,
            #[cfg(not(armv6m))]
            Exception::DebugMonitor => -4,
            Exception::PendSV => -2,
            Exception::SysTick => -1,
        }
    }
}

/// Active exception number
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[cfg_attr(feature = "serde", derive(Serialize, Deserialize))]
#[cfg_attr(feature = "std", derive(PartialOrd, Hash))]
pub enum VectActive {
    /// Thread mode
    ThreadMode,

    /// Processor core exception (internal interrupts)
    Exception(Exception),

    /// Device specific exception (external interrupts)
    Interrupt {
        /// Interrupt number. This number is always within half open range `[0, 240)`
        irqn: u8,
    },
}

impl VectActive {
    /// Converts a `byte` into `VectActive`
    #[inline]
    pub fn from(vect_active: u8) -> Option<Self> {
        Some(match vect_active {
            0 => VectActive::ThreadMode,
            2 => VectActive::Exception(Exception::NonMaskableInt),
            3 => VectActive::Exception(Exception::HardFault),
            #[cfg(not(armv6m))]
            4 => VectActive::Exception(Exception::MemoryManagement),
            #[cfg(not(armv6m))]
            5 => VectActive::Exception(Exception::BusFault),
            #[cfg(not(armv6m))]
            6 => VectActive::Exception(Exception::UsageFault),
            #[cfg(any(armv8m, native))]
            7 => VectActive::Exception(Exception::SecureFault),
            11 => VectActive::Exception(Exception::SVCall),
            #[cfg(not(armv6m))]
            12 => VectActive::Exception(Exception::DebugMonitor),
            14 => VectActive::Exception(Exception::PendSV),
            15 => VectActive::Exception(Exception::SysTick),
            irqn if irqn >= 16 => VectActive::Interrupt { irqn },
            _ => return None,
        })
    }
}

#[cfg(not(armv6m))]
mod scb_consts {
    pub const SCB_CCR_IC_MASK: u32 = 1 << 17;
    pub const SCB_CCR_DC_MASK: u32 = 1 << 16;
}

#[cfg(not(armv6m))]
use self::scb_consts::*;

#[cfg(not(armv6m))]
impl SCB {
    /// Enables I-cache if currently disabled.
    ///
    /// This operation first invalidates the entire I-cache.
    #[inline]
    pub fn enable_icache(&mut self) {
        // Don't do anything if I-cache is already enabled
        if Self::icache_enabled() {
            return;
        }

        // NOTE(unsafe): No races as all CBP registers are write-only and stateless
        let mut cbp = unsafe { CBP::new() };

        // Invalidate I-cache
        cbp.iciallu();

        // Enable I-cache
        extern "C" {
            // see asm-v7m.s
            fn __enable_icache();
        }

        // NOTE(unsafe): The asm routine manages exclusive access to the SCB
        // registers and applies the proper barriers; it is technically safe on
        // its own, and is only `unsafe` here because it's `extern "C"`.
        unsafe {
            __enable_icache();
        }
    }

    /// Disables I-cache if currently enabled.
    ///
    /// This operation invalidates the entire I-cache after disabling.
    #[inline]
    pub fn disable_icache(&mut self) {
        // Don't do anything if I-cache is already disabled
        if !Self::icache_enabled() {
            return;
        }

        // NOTE(unsafe): No races as all CBP registers are write-only and stateless
        let mut cbp = unsafe { CBP::new() };

        // Disable I-cache
        // NOTE(unsafe): We have synchronised access by &mut self
        unsafe { self.ccr.modify(|r| r & !SCB_CCR_IC_MASK) };

        // Invalidate I-cache
        cbp.iciallu();

        crate::asm::dsb();
        crate::asm::isb();
    }

    /// Returns whether the I-cache is currently enabled.
    #[inline(always)]
    pub fn icache_enabled() -> bool {
        crate::asm::dsb();
        crate::asm::isb();

        // NOTE(unsafe): atomic read with no side effects
        unsafe { (*Self::PTR).ccr.read() & SCB_CCR_IC_MASK == SCB_CCR_IC_MASK }
    }

    /// Invalidates the entire I-cache.
    #[inline]
    pub fn invalidate_icache(&mut self) {
        // NOTE(unsafe): No races as all CBP registers are write-only and stateless
        let mut cbp = unsafe { CBP::new() };

        // Invalidate I-cache
        cbp.iciallu();

        crate::asm::dsb();
        crate::asm::isb();
    }

    /// Enables D-cache if currently disabled.
    ///
    /// This operation first invalidates the entire D-cache, ensuring it does
    /// not contain stale values before being enabled.
    #[inline]
    pub fn enable_dcache(&mut self, cpuid: &mut CPUID) {
        // Don't do anything if D-cache is already enabled
        if Self::dcache_enabled() {
            return;
        }

        // Invalidate anything currently in the D-cache
        unsafe { self.invalidate_dcache(cpuid) };

        // Now turn on the D-cache
        extern "C" {
            // see asm-v7m.s
            fn __enable_dcache();
        }

        // NOTE(unsafe): The asm routine manages exclusive access to the SCB
        // registers and applies the proper barriers; it is technically safe on
        // its own, and is only `unsafe` here because it's `extern "C"`.
        unsafe {
            __enable_dcache();
        }
    }

    /// Disables D-cache if currently enabled.
    ///
    /// This operation subsequently cleans and invalidates the entire D-cache,
    /// ensuring all contents are safely written back to main memory after disabling.
    #[inline]
    pub fn disable_dcache(&mut self, cpuid: &mut CPUID) {
        // Don't do anything if D-cache is already disabled
        if !Self::dcache_enabled() {
            return;
        }

        // Turn off the D-cache
        // NOTE(unsafe): We have synchronised access by &mut self
        unsafe { self.ccr.modify(|r| r & !SCB_CCR_DC_MASK) };

        // Clean and invalidate whatever was left in it
        self.clean_invalidate_dcache(cpuid);
    }

    /// Returns whether the D-cache is currently enabled.
    #[inline]
    pub fn dcache_enabled() -> bool {
        crate::asm::dsb();
        crate::asm::isb();

        // NOTE(unsafe) atomic read with no side effects
        unsafe { (*Self::PTR).ccr.read() & SCB_CCR_DC_MASK == SCB_CCR_DC_MASK }
    }

    /// Invalidates the entire D-cache.
    ///
    /// Note that calling this while the dcache is enabled will probably wipe out the
    /// stack, depending on optimisations, therefore breaking returning to the call point.
    ///
    /// It's used immediately before enabling the dcache, but not exported publicly.
    #[inline]
    unsafe fn invalidate_dcache(&mut self, cpuid: &mut CPUID) {
        // NOTE(unsafe): No races as all CBP registers are write-only and stateless
        let mut cbp = CBP::new();

        // Read number of sets and ways
        let (sets, ways) = cpuid.cache_num_sets_ways(0, CsselrCacheType::DataOrUnified);

        // Invalidate entire D-cache
        for set in 0..sets {
            for way in 0..ways {
                cbp.dcisw(set, way);
            }
        }

        crate::asm::dsb();
        crate::asm::isb();
    }

    /// Cleans the entire D-cache.
    ///
    /// This function causes everything in the D-cache to be written back to main memory,
    /// overwriting whatever is already there.
    #[inline]
    pub fn clean_dcache(&mut self, cpuid: &mut CPUID) {
        // NOTE(unsafe): No races as all CBP registers are write-only and stateless
        let mut cbp = unsafe { CBP::new() };

        // Read number of sets and ways
        let (sets, ways) = cpuid.cache_num_sets_ways(0, CsselrCacheType::DataOrUnified);

        for set in 0..sets {
            for way in 0..ways {
                cbp.dccsw(set, way);
            }
        }

        crate::asm::dsb();
        crate::asm::isb();
    }

    /// Cleans and invalidates the entire D-cache.
    ///
    /// This function causes everything in the D-cache to be written back to main memory,
    /// and then marks the entire D-cache as invalid, causing future reads to first fetch
    /// from main memory.
    #[inline]
    pub fn clean_invalidate_dcache(&mut self, cpuid: &mut CPUID) {
        // NOTE(unsafe): No races as all CBP registers are write-only and stateless
        let mut cbp = unsafe { CBP::new() };

        // Read number of sets and ways
        let (sets, ways) = cpuid.cache_num_sets_ways(0, CsselrCacheType::DataOrUnified);

        for set in 0..sets {
            for way in 0..ways {
                cbp.dccisw(set, way);
            }
        }

        crate::asm::dsb();
        crate::asm::isb();
    }

    /// Invalidates D-cache by address.
    ///
    /// * `addr`: The address to invalidate, which must be cache-line aligned.
    /// * `size`: Number of bytes to invalidate, which must be a multiple of the cache line size.
    ///
    /// Invalidates D-cache cache lines, starting from the first line containing `addr`,
    /// finishing once at least `size` bytes have been invalidated.
    ///
    /// Invalidation causes the next read access to memory to be fetched from main memory instead
    /// of the cache.
    ///
    /// # Cache Line Sizes
    ///
    /// Cache line sizes vary by core. For all Cortex-M7 cores, the cache line size is fixed
    /// to 32 bytes, which means `addr` must be 32-byte aligned and `size` must be a multiple
    /// of 32. At the time of writing, no other Cortex-M cores have data caches.
    ///
    /// If `addr` is not cache-line aligned, or `size` is not a multiple of the cache line size,
    /// other data before or after the desired memory would also be invalidated, which can very
    /// easily cause memory corruption and undefined behaviour.
    ///
    /// # Safety
    ///
    /// After invalidating, the next read of invalidated data will be from main memory. This may
    /// cause recent writes to be lost, potentially including writes that initialized objects.
    /// Therefore, this method may cause uninitialized memory or invalid values to be read,
    /// resulting in undefined behaviour. You must ensure that main memory contains valid and
    /// initialized values before invalidating.
    ///
    /// `addr` **must** be aligned to the size of the cache lines, and `size` **must** be a
    /// multiple of the cache line size, otherwise this function will invalidate other memory,
    /// easily leading to memory corruption and undefined behaviour. This precondition is checked
    /// in debug builds using a `debug_assert!()`, but not checked in release builds to avoid
    /// a runtime-dependent `panic!()` call.
    #[inline]
    pub unsafe fn invalidate_dcache_by_address(&mut self, addr: usize, size: usize) {
        // No-op zero sized operations
        if size == 0 {
            return;
        }

        // NOTE(unsafe): No races as all CBP registers are write-only and stateless
        let mut cbp = CBP::new();

        // dminline is log2(num words), so 2**dminline * 4 gives size in bytes
        let dminline = CPUID::cache_dminline();
        let line_size = (1 << dminline) * 4;

        debug_assert!((addr & (line_size - 1)) == 0);
        debug_assert!((size & (line_size - 1)) == 0);

        crate::asm::dsb();

        // Find number of cache lines to invalidate
        let num_lines = ((size - 1) / line_size) + 1;

        // Compute address of first cache line
        let mask = 0xFFFF_FFFF - (line_size - 1);
        let mut addr = addr & mask;

        for _ in 0..num_lines {
            cbp.dcimvac(addr as u32);
            addr += line_size;
        }

        crate::asm::dsb();
        crate::asm::isb();
    }

    /// Invalidates an object from the D-cache.
    ///
    /// * `obj`: The object to invalidate.
    ///
    /// Invalidates D-cache starting from the first cache line containing `obj`,
    /// continuing to invalidate cache lines until all of `obj` has been invalidated.
    ///
    /// Invalidation causes the next read access to memory to be fetched from main memory instead
    /// of the cache.
    ///
    /// # Cache Line Sizes
    ///
    /// Cache line sizes vary by core. For all Cortex-M7 cores, the cache line size is fixed
    /// to 32 bytes, which means `obj` must be 32-byte aligned, and its size must be a multiple
    /// of 32 bytes. At the time of writing, no other Cortex-M cores have data caches.
    ///
    /// If `obj` is not cache-line aligned, or its size is not a multiple of the cache line size,
    /// other data before or after the desired memory would also be invalidated, which can very
    /// easily cause memory corruption and undefined behaviour.
    ///
    /// # Safety
    ///
    /// After invalidating, `obj` will be read from main memory on next access. This may cause
    /// recent writes to `obj` to be lost, potentially including the write that initialized it.
    /// Therefore, this method may cause uninitialized memory or invalid values to be read,
    /// resulting in undefined behaviour. You must ensure that main memory contains a valid and
    /// initialized value for T before invalidating `obj`.
    ///
    /// `obj` **must** be aligned to the size of the cache lines, and its size **must** be a
    /// multiple of the cache line size, otherwise this function will invalidate other memory,
    /// easily leading to memory corruption and undefined behaviour. This precondition is checked
    /// in debug builds using a `debug_assert!()`, but not checked in release builds to avoid
    /// a runtime-dependent `panic!()` call.
    #[inline]
    pub unsafe fn invalidate_dcache_by_ref<T>(&mut self, obj: &mut T) {
        self.invalidate_dcache_by_address(obj as *const T as usize, core::mem::size_of::<T>());
    }

    /// Invalidates a slice from the D-cache.
    ///
    /// * `slice`: The slice to invalidate.
    ///
    /// Invalidates D-cache starting from the first cache line containing members of `slice`,
    /// continuing to invalidate cache lines until all of `slice` has been invalidated.
    ///
    /// Invalidation causes the next read access to memory to be fetched from main memory instead
    /// of the cache.
    ///
    /// # Cache Line Sizes
    ///
    /// Cache line sizes vary by core. For all Cortex-M7 cores, the cache line size is fixed
    /// to 32 bytes, which means `slice` must be 32-byte aligned, and its size must be a multiple
    /// of 32 bytes. At the time of writing, no other Cortex-M cores have data caches.
    ///
    /// If `slice` is not cache-line aligned, or its size is not a multiple of the cache line size,
    /// other data before or after the desired memory would also be invalidated, which can very
    /// easily cause memory corruption and undefined behaviour.
    ///
    /// # Safety
    ///
    /// After invalidating, `slice` will be read from main memory on next access. This may cause
    /// recent writes to `slice` to be lost, potentially including the write that initialized it.
    /// Therefore, this method may cause uninitialized memory or invalid values to be read,
    /// resulting in undefined behaviour. You must ensure that main memory contains valid and
    /// initialized values for T before invalidating `slice`.
    ///
    /// `slice` **must** be aligned to the size of the cache lines, and its size **must** be a
    /// multiple of the cache line size, otherwise this function will invalidate other memory,
    /// easily leading to memory corruption and undefined behaviour. This precondition is checked
    /// in debug builds using a `debug_assert!()`, but not checked in release builds to avoid
    /// a runtime-dependent `panic!()` call.
    #[inline]
    pub unsafe fn invalidate_dcache_by_slice<T>(&mut self, slice: &mut [T]) {
        self.invalidate_dcache_by_address(
            slice.as_ptr() as usize,
            slice.len() * core::mem::size_of::<T>(),
        );
    }

    /// Cleans D-cache by address.
    ///
    /// * `addr`: The address to start cleaning at.
    /// * `size`: The number of bytes to clean.
    ///
    /// Cleans D-cache cache lines, starting from the first line containing `addr`,
    /// finishing once at least `size` bytes have been invalidated.
    ///
    /// Cleaning the cache causes whatever data is present in the cache to be immediately written
    /// to main memory, overwriting whatever was in main memory.
    ///
    /// # Cache Line Sizes
    ///
    /// Cache line sizes vary by core. For all Cortex-M7 cores, the cache line size is fixed
    /// to 32 bytes, which means `addr` should generally be 32-byte aligned and `size` should be a
    /// multiple of 32. At the time of writing, no other Cortex-M cores have data caches.
    ///
    /// If `addr` is not cache-line aligned, or `size` is not a multiple of the cache line size,
    /// other data before or after the desired memory will also be cleaned. From the point of view
    /// of the core executing this function, memory remains consistent, so this is not unsound,
    /// but is worth knowing about.
    #[inline]
    pub fn clean_dcache_by_address(&mut self, addr: usize, size: usize) {
        // No-op zero sized operations
        if size == 0 {
            return;
        }

        // NOTE(unsafe): No races as all CBP registers are write-only and stateless
        let mut cbp = unsafe { CBP::new() };

        crate::asm::dsb();

        let dminline = CPUID::cache_dminline();
        let line_size = (1 << dminline) * 4;
        let num_lines = ((size - 1) / line_size) + 1;

        let mask = 0xFFFF_FFFF - (line_size - 1);
        let mut addr = addr & mask;

        for _ in 0..num_lines {
            cbp.dccmvac(addr as u32);
            addr += line_size;
        }

        crate::asm::dsb();
        crate::asm::isb();
    }

    /// Cleans an object from the D-cache.
    ///
    /// * `obj`: The object to clean.
    ///
    /// Cleans D-cache starting from the first cache line containing `obj`,
    /// continuing to clean cache lines until all of `obj` has been cleaned.
    ///
    /// It is recommended that `obj` is both aligned to the cache line size and a multiple of
    /// the cache line size long, otherwise surrounding data will also be cleaned.
    ///
    /// Cleaning the cache causes whatever data is present in the cache to be immediately written
    /// to main memory, overwriting whatever was in main memory.
    #[inline]
    pub fn clean_dcache_by_ref<T>(&mut self, obj: &T) {
        self.clean_dcache_by_address(obj as *const T as usize, core::mem::size_of::<T>());
    }

    /// Cleans a slice from D-cache.
    ///
    /// * `slice`: The slice to clean.
    ///
    /// Cleans D-cache starting from the first cache line containing members of `slice`,
    /// continuing to clean cache lines until all of `slice` has been cleaned.
    ///
    /// It is recommended that `slice` is both aligned to the cache line size and a multiple of
    /// the cache line size long, otherwise surrounding data will also be cleaned.
    ///
    /// Cleaning the cache causes whatever data is present in the cache to be immediately written
    /// to main memory, overwriting whatever was in main memory.
    #[inline]
    pub fn clean_dcache_by_slice<T>(&mut self, slice: &[T]) {
        self.clean_dcache_by_address(
            slice.as_ptr() as usize,
            slice.len() * core::mem::size_of::<T>(),
        );
    }

    /// Cleans and invalidates D-cache by address.
    ///
    /// * `addr`: The address to clean and invalidate.
    /// * `size`: The number of bytes to clean and invalidate.
    ///
    /// Cleans and invalidates D-cache starting from the first cache line containing `addr`,
    /// finishing once at least `size` bytes have been cleaned and invalidated.
    ///
    /// It is recommended that `addr` is aligned to the cache line size and `size` is a multiple of
    /// the cache line size, otherwise surrounding data will also be cleaned.
    ///
    /// Cleaning and invalidating causes data in the D-cache to be written back to main memory,
    /// and then marks that data in the D-cache as invalid, causing future reads to first fetch
    /// from main memory.
    #[inline]
    pub fn clean_invalidate_dcache_by_address(&mut self, addr: usize, size: usize) {
        // No-op zero sized operations
        if size == 0 {
            return;
        }

        // NOTE(unsafe): No races as all CBP registers are write-only and stateless
        let mut cbp = unsafe { CBP::new() };

        crate::asm::dsb();

        // Cache lines are fixed to 32 bit on Cortex-M7 and not present in earlier Cortex-M
        const LINESIZE: usize = 32;
        let num_lines = ((size - 1) / LINESIZE) + 1;

        let mut addr = addr & 0xFFFF_FFE0;

        for _ in 0..num_lines {
            cbp.dccimvac(addr as u32);
            addr += LINESIZE;
        }

        crate::asm::dsb();
        crate::asm::isb();
    }
}

const SCB_SCR_SLEEPDEEP: u32 = 0x1 << 2;

impl SCB {
    /// Set the SLEEPDEEP bit in the SCR register
    #[inline]
    pub fn set_sleepdeep(&mut self) {
        unsafe {
            self.scr.modify(|scr| scr | SCB_SCR_SLEEPDEEP);
        }
    }

    /// Clear the SLEEPDEEP bit in the SCR register
    #[inline]
    pub fn clear_sleepdeep(&mut self) {
        unsafe {
            self.scr.modify(|scr| scr & !SCB_SCR_SLEEPDEEP);
        }
    }
}

const SCB_SCR_SLEEPONEXIT: u32 = 0x1 << 1;

impl SCB {
    /// Set the SLEEPONEXIT bit in the SCR register
    #[inline]
    pub fn set_sleeponexit(&mut self) {
        unsafe {
            self.scr.modify(|scr| scr | SCB_SCR_SLEEPONEXIT);
        }
    }

    /// Clear the SLEEPONEXIT bit in the SCR register
    #[inline]
    pub fn clear_sleeponexit(&mut self) {
        unsafe {
            self.scr.modify(|scr| scr & !SCB_SCR_SLEEPONEXIT);
        }
    }
}

const SCB_AIRCR_VECTKEY: u32 = 0x05FA << 16;
const SCB_AIRCR_PRIGROUP_MASK: u32 = 0x7 << 8;
const SCB_AIRCR_SYSRESETREQ: u32 = 1 << 2;

impl SCB {
    /// Initiate a system reset request to reset the MCU
    #[inline]
    pub fn sys_reset() -> ! {
        crate::asm::dsb();
        unsafe {
            (*Self::PTR).aircr.modify(
                |r| {
                    SCB_AIRCR_VECTKEY | // otherwise the write is ignored
            r & SCB_AIRCR_PRIGROUP_MASK | // keep priority group unchanged
            SCB_AIRCR_SYSRESETREQ
                }, // set the bit
            )
        };
        crate::asm::dsb();
        loop {
            // wait for the reset
            crate::asm::nop(); // avoid rust-lang/rust#28728
        }
    }
}

const SCB_ICSR_PENDSVSET: u32 = 1 << 28;
const SCB_ICSR_PENDSVCLR: u32 = 1 << 27;

const SCB_ICSR_PENDSTSET: u32 = 1 << 26;
const SCB_ICSR_PENDSTCLR: u32 = 1 << 25;

impl SCB {
    /// Set the PENDSVSET bit in the ICSR register which will pend the PendSV interrupt
    #[inline]
    pub fn set_pendsv() {
        unsafe {
            (*Self::PTR).icsr.write(SCB_ICSR_PENDSVSET);
        }
    }

    /// Check if PENDSVSET bit in the ICSR register is set meaning PendSV interrupt is pending
    #[inline]
    pub fn is_pendsv_pending() -> bool {
        unsafe { (*Self::PTR).icsr.read() & SCB_ICSR_PENDSVSET == SCB_ICSR_PENDSVSET }
    }

    /// Set the PENDSVCLR bit in the ICSR register which will clear a pending PendSV interrupt
    #[inline]
    pub fn clear_pendsv() {
        unsafe {
            (*Self::PTR).icsr.write(SCB_ICSR_PENDSVCLR);
        }
    }

    /// Set the PENDSTSET bit in the ICSR register which will pend a SysTick interrupt
    #[inline]
    pub fn set_pendst() {
        unsafe {
            (*Self::PTR).icsr.write(SCB_ICSR_PENDSTSET);
        }
    }

    /// Check if PENDSTSET bit in the ICSR register is set meaning SysTick interrupt is pending
    #[inline]
    pub fn is_pendst_pending() -> bool {
        unsafe { (*Self::PTR).icsr.read() & SCB_ICSR_PENDSTSET == SCB_ICSR_PENDSTSET }
    }

    /// Set the PENDSTCLR bit in the ICSR register which will clear a pending SysTick interrupt
    #[inline]
    pub fn clear_pendst() {
        unsafe {
            (*Self::PTR).icsr.write(SCB_ICSR_PENDSTCLR);
        }
    }
}

/// System handlers, exceptions with configurable priority
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[repr(u8)]
pub enum SystemHandler {
    // NonMaskableInt, // priority is fixed
    // HardFault, // priority is fixed
    /// Memory management interrupt (not present on Cortex-M0 variants)
    #[cfg(not(armv6m))]
    MemoryManagement = 4,

    /// Bus fault interrupt (not present on Cortex-M0 variants)
    #[cfg(not(armv6m))]
    BusFault = 5,

    /// Usage fault interrupt (not present on Cortex-M0 variants)
    #[cfg(not(armv6m))]
    UsageFault = 6,

    /// Secure fault interrupt (only on ARMv8-M)
    #[cfg(any(armv8m, native))]
    SecureFault = 7,

    /// SV call interrupt
    SVCall = 11,

    /// Debug monitor interrupt (not present on Cortex-M0 variants)
    #[cfg(not(armv6m))]
    DebugMonitor = 12,

    /// Pend SV interrupt
    PendSV = 14,

    /// System Tick interrupt
    SysTick = 15,
}

impl SCB {
    /// Returns the hardware priority of `system_handler`
    ///
    /// *NOTE*: Hardware priority does not exactly match logical priority levels. See
    /// [`NVIC.get_priority`](struct.NVIC.html#method.get_priority) for more details.
    #[inline]
    pub fn get_priority(system_handler: SystemHandler) -> u8 {
        let index = system_handler as u8;

        #[cfg(not(armv6m))]
        {
            // NOTE(unsafe) atomic read with no side effects

            // NOTE(unsafe): Index is bounded to [4,15] by SystemHandler design.
            // TODO: Review it after rust-lang/rust/issues/13926 will be fixed.
            let priority_ref = unsafe { (*Self::PTR).shpr.get_unchecked(usize::from(index - 4)) };

            priority_ref.read()
        }

        #[cfg(armv6m)]
        {
            // NOTE(unsafe) atomic read with no side effects

            // NOTE(unsafe): Index is bounded to [11,15] by SystemHandler design.
            // TODO: Review it after rust-lang/rust/issues/13926 will be fixed.
            let priority_ref = unsafe {
                (*Self::PTR)
                    .shpr
                    .get_unchecked(usize::from((index - 8) / 4))
            };

            let shpr = priority_ref.read();
            let prio = (shpr >> (8 * (index % 4))) & 0x0000_00ff;
            prio as u8
        }
    }

    /// Sets the hardware priority of `system_handler` to `prio`
    ///
    /// *NOTE*: Hardware priority does not exactly match logical priority levels. See
    /// [`NVIC.get_priority`](struct.NVIC.html#method.get_priority) for more details.
    ///
    /// On ARMv6-M, updating a system handler priority requires a read-modify-write operation. On
    /// ARMv7-M, the operation is performed in a single, atomic write operation.
    ///
    /// # Unsafety
    ///
    /// Changing priority levels can break priority-based critical sections (see
    /// [`register::basepri`](crate::register::basepri)) and compromise memory safety.
    #[inline]
    pub unsafe fn set_priority(&mut self, system_handler: SystemHandler, prio: u8) {
        let index = system_handler as u8;

        #[cfg(not(armv6m))]
        {
            // NOTE(unsafe): Index is bounded to [4,15] by SystemHandler design.
            // TODO: Review it after rust-lang/rust/issues/13926 will be fixed.
            let priority_ref = (*Self::PTR).shpr.get_unchecked(usize::from(index - 4));

            priority_ref.write(prio)
        }

        #[cfg(armv6m)]
        {
            // NOTE(unsafe): Index is bounded to [11,15] by SystemHandler design.
            // TODO: Review it after rust-lang/rust/issues/13926 will be fixed.
            let priority_ref = (*Self::PTR)
                .shpr
                .get_unchecked(usize::from((index - 8) / 4));

            priority_ref.modify(|value| {
                let shift = 8 * (index % 4);
                let mask = 0x0000_00ff << shift;
                let prio = u32::from(prio) << shift;

                (value & !mask) | prio
            });
        }
    }

    /// Return the bit position of the exception enable bit in the SHCSR register
    #[inline]
    #[cfg(not(any(armv6m, armv8m_base)))]
    fn shcsr_enable_shift(exception: Exception) -> Option<u32> {
        match exception {
            Exception::MemoryManagement => Some(16),
            Exception::BusFault => Some(17),
            Exception::UsageFault => Some(18),
            #[cfg(armv8m_main)]
            Exception::SecureFault => Some(19),
            _ => None,
        }
    }

    /// Enable the exception
    ///
    /// If the exception is enabled, when the exception is triggered, the exception handler will be executed instead of the
    /// HardFault handler.
    /// This function is only allowed on the following exceptions:
    /// * `MemoryManagement`
    /// * `BusFault`
    /// * `UsageFault`
    /// * `SecureFault` (can only be enabled from Secure state)
    ///
    /// Calling this function with any other exception will do nothing.
    #[inline]
    #[cfg(not(any(armv6m, armv8m_base)))]
    pub fn enable(&mut self, exception: Exception) {
        if let Some(shift) = SCB::shcsr_enable_shift(exception) {
            // The mutable reference to SCB makes sure that only this code is currently modifying
            // the register.
            unsafe { self.shcsr.modify(|value| value | (1 << shift)) }
        }
    }

    /// Disable the exception
    ///
    /// If the exception is disabled, when the exception is triggered, the HardFault handler will be executed instead of the
    /// exception handler.
    /// This function is only allowed on the following exceptions:
    /// * `MemoryManagement`
    /// * `BusFault`
    /// * `UsageFault`
    /// * `SecureFault` (can not be changed from Non-secure state)
    ///
    /// Calling this function with any other exception will do nothing.
    #[inline]
    #[cfg(not(any(armv6m, armv8m_base)))]
    pub fn disable(&mut self, exception: Exception) {
        if let Some(shift) = SCB::shcsr_enable_shift(exception) {
            // The mutable reference to SCB makes sure that only this code is currently modifying
            // the register.
            unsafe { self.shcsr.modify(|value| value & !(1 << shift)) }
        }
    }

    /// Check if an exception is enabled
    ///
    /// This function is only allowed on the following exception:
    /// * `MemoryManagement`
    /// * `BusFault`
    /// * `UsageFault`
    /// * `SecureFault` (can not be read from Non-secure state)
    ///
    /// Calling this function with any other exception will read `false`.
    #[inline]
    #[cfg(not(any(armv6m, armv8m_base)))]
    pub fn is_enabled(&self, exception: Exception) -> bool {
        if let Some(shift) = SCB::shcsr_enable_shift(exception) {
            (self.shcsr.read() & (1 << shift)) > 0
        } else {
            false
        }
    }
}
