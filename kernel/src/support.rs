// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
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

use crate::{
    arch,
    sync::spinlock::{SpinLock, SpinLockGuard},
    thread::ThreadNode,
    types::{Arc, ArcList, AtomicUint, IntrusiveAdapter, Uint},
};
use core::{
    alloc::Layout,
    mem::MaybeUninit,
    ptr::NonNull,
    sync::atomic::{compiler_fence, AtomicUsize, Ordering},
};

#[derive(Debug)]
pub(crate) struct DisableInterruptGuard {
    old: usize,
}

impl DisableInterruptGuard {
    #[inline]
    pub fn new() -> Self {
        Self {
            old: arch::disable_local_irq_save(),
        }
    }
}

impl Drop for DisableInterruptGuard {
    #[inline]
    fn drop(&mut self) {
        arch::enable_local_irq_restore(self.old);
    }
}

pub(crate) struct PlainDisableInterruptGuard;

impl PlainDisableInterruptGuard {
    #[inline]
    pub fn new() -> Self {
        arch::disable_local_irq();
        Self
    }
}

impl Drop for PlainDisableInterruptGuard {
    #[inline]
    fn drop(&mut self) {
        arch::enable_local_irq();
    }
}

pub(crate) struct ScopeTimer {}

#[derive(Default, Copy, Debug, Clone)]
pub(crate) struct Region {
    pub base: usize,
    pub size: usize,
}

pub(crate) struct RegionalObjectBuilder {
    unfilled_region: Region,
}

impl RegionalObjectBuilder {
    #[inline]
    pub fn new(region: Region) -> Self {
        Self {
            unfilled_region: region,
        }
    }

    // FIXME: We should consider adding lifetime limit on self.region
    // and returned value should have the same lifetime as the
    // self.region.
    pub fn write_before_end<T: Sized>(&mut self, val: T) -> Option<&'static mut T> {
        let sz = core::mem::size_of::<T>();
        if self.unfilled_region.size < sz {
            return None;
        }
        let align = core::mem::align_of::<T>();
        let start = (self.unfilled_region.base + self.unfilled_region.size - sz) & (!align);
        if start < self.unfilled_region.base {
            return None;
        }
        let ptr = start as *mut T;
        assert_eq!(ptr.align_offset(align), 0, "Must be aligned");
        unsafe { ptr.write(val) };
        self.unfilled_region.size = start - self.unfilled_region.base;
        Some(unsafe { &mut *ptr })
    }

    pub fn write_after_start<T: Sized>(&mut self, val: T) -> Option<&'static mut T> {
        let sz = core::mem::size_of::<T>();
        if self.unfilled_region.size < sz {
            return None;
        }
        let align = core::mem::align_of::<T>();
        let padding = (align - self.unfilled_region.base % align) % align;
        let start = self.unfilled_region.base + padding;
        let end = self.unfilled_region.base + self.unfilled_region.size;
        if start + sz > end {
            return None;
        }
        let ptr = start as *mut T;
        assert_eq!(ptr.align_offset(align), 0, "Must be aligned");
        unsafe { ptr.write(val) };
        self.unfilled_region.base = start + sz;
        self.unfilled_region.size = end - self.unfilled_region.base;
        Some(unsafe { &mut *ptr })
    }

    // FIXME: Should return MaybeUninint<T>?
    pub fn zeroed_after_start<T: Sized>(&mut self) -> Option<&'static mut T> {
        let sz = core::mem::size_of::<T>();
        if self.unfilled_region.size < sz {
            return None;
        }
        let align = core::mem::align_of::<T>();
        let padding = (align - self.unfilled_region.base % align) % align;
        let start = self.unfilled_region.base + padding;
        let end = self.unfilled_region.base + self.unfilled_region.size;
        if start + sz > end {
            return None;
        }
        let ptr = start as *mut u8;
        assert_eq!(ptr.align_offset(align), 0, "Must be aligned");
        let slice = unsafe { core::slice::from_raw_parts_mut(ptr, sz) };
        slice.fill(0u8);
        self.unfilled_region.base = start + sz;
        self.unfilled_region.size = end - self.unfilled_region.base;
        Some(unsafe { &mut *(ptr as *mut T) })
    }

    pub fn get_aligned_region_end(&self, align: usize) -> usize {
        (self.unfilled_region.base + self.unfilled_region.size) & (!align)
    }

    pub fn get_aligned_region_start(&self, align: usize) -> usize {
        let padding = (align - self.unfilled_region.base % align) % align;
        self.unfilled_region.base + padding
    }
}

pub(crate) struct MemoryPartitioner {
    base: usize,
    size: usize,
    num_parts: usize,
}

impl MemoryPartitioner {
    #[inline]
    pub fn new(start: usize, end: usize, n: usize) -> Self {
        let size = end - start;
        assert!(size % n == 0, "Unable to divide the region evenly");
        Self {
            base: start,
            size,
            num_parts: n,
        }
    }

    #[inline(always)]
    pub fn get_part(&self, i: usize) -> Option<Region> {
        if i >= self.num_parts {
            return None;
        }
        let part = self.size / self.num_parts;
        Some(Region {
            base: self.base + i * part,
            size: part,
        })
    }
}

#[inline]
pub const fn align_down_size(addr: usize, align: usize) -> usize {
    addr & !(align - 1)
}

#[inline]
pub const fn align_up_size(addr: usize, align: usize) -> usize {
    (addr + align - 1) & !(align - 1)
}

#[inline]
pub fn align_up(addr: *mut u8, align: usize) -> *mut u8 {
    align_up_size(addr as usize, align) as *mut u8
}

#[inline]
pub const fn align_offset(addr: usize, align: usize) -> usize {
    addr & (align - 1)
}

#[inline]
pub const fn is_aligned(addr: usize, align: usize) -> bool {
    align_offset(addr, align) == 0
}

/// Polyfill for <https://github.com/rust-lang/rust/issues/71941>
#[inline]
pub fn nonnull_slice_from_raw_parts<T>(ptr: NonNull<T>, len: usize) -> NonNull<[T]> {
    unsafe { NonNull::new_unchecked(core::ptr::slice_from_raw_parts_mut(ptr.as_ptr(), len)) }
}

/// Polyfill for <https://github.com/rust-lang/rust/issues/71146>
#[inline]
pub fn nonnull_slice_len<T>(ptr: NonNull<[T]>) -> usize {
    // Safety: We are just reading the slice length embedded in the fat
    //         pointer and not dereferencing the pointer. We also convert it
    //         to `*mut [MaybeUninit<u8>]` just in case because the slice
    //         might be uninitialized.
    unsafe { (*(ptr.as_ptr() as *const [MaybeUninit<T>])).len() }
}

/// Polyfill for <https://github.com/rust-lang/rust/issues/74265>
#[inline]
pub fn nonnull_slice_start<T>(ptr: NonNull<[T]>) -> NonNull<T> {
    unsafe { NonNull::new_unchecked(ptr.as_ptr() as *mut T) }
}

#[inline]
pub fn nonnull_slice_end<T>(ptr: NonNull<[T]>) -> *mut T {
    (ptr.as_ptr() as *mut T).wrapping_add(nonnull_slice_len(ptr))
}

pub(crate) struct PerCpuVarAccessGuard {
    t: ThreadNode,
    id: u8,
}

impl PerCpuVarAccessGuard {
    pub fn new() -> Self {
        let dig = DisableInterruptGuard::new();
        let id = arch::current_cpu_id();
        let t = unsafe {
            crate::scheduler::RUNNING_THREADS[id]
                .assume_init_ref()
                .clone()
        };
        t.disable_preempt();
        compiler_fence(Ordering::SeqCst);
        drop(dig);
        Self { t, id: id as u8 }
    }

    #[inline(always)]
    pub fn id(&self) -> usize {
        self.id as usize
    }
}

impl Drop for PerCpuVarAccessGuard {
    #[inline]
    fn drop(&mut self) {
        self.t.enable_preempt();
    }
}

pub(crate) struct ArcBufferingQueue<T: Sized, A: IntrusiveAdapter, const N: usize> {
    queues: [SpinLock<ArcList<T, A>>; N],
    active: AtomicUint,
}

impl<T: Sized, A: IntrusiveAdapter, const N: usize> Init for ArcBufferingQueue<T, A, N> {
    fn init(&mut self) -> bool {
        self.init_queues() == N
    }
}

impl<T: Sized, A: IntrusiveAdapter, const N: usize> ArcBufferingQueue<T, A, N> {
    #[inline]
    pub const fn new() -> Self {
        Self {
            queues: [const { SpinLock::new(ArcList::new()) }; N],
            active: AtomicUint::new(0),
        }
    }

    pub fn init_queues(&self) -> usize {
        let mut res = 0;
        for i in 0..N {
            if self.queues[i].lock().init() {
                res += 1;
            }
        }
        res
    }

    pub type WorkList = ArcList<T, A>;

    #[inline]
    #[allow(clippy::unnecessary_cast)]
    pub fn advance_active_queue(&self) -> SpinLockGuard<'_, ArcList<T, A>> {
        let i = self.active.fetch_add(1, Ordering::AcqRel) as usize;
        self.queues[i % N].irqsave_lock()
    }

    #[inline]
    #[allow(clippy::unnecessary_cast)]
    pub fn get_active_queue(&self) -> SpinLockGuard<'_, ArcList<T, A>> {
        let i = self.active.load(Ordering::Acquire) as usize;
        self.queues[i % N].irqsave_lock()
    }
}

pub trait Init {
    fn init(&mut self) -> bool;
}

pub struct PerCpu<T: Sized, const N: usize> {
    data: [T; N],
}

unsafe impl<T: Sized, const N: usize> Send for PerCpu<T, N> {}
unsafe impl<T: Sized, const N: usize> Sync for PerCpu<T, N> {}

impl<T: Sized, const N: usize> PerCpu<T, N> {
    pub const fn new(data: [T; N]) -> Self {
        Self { data }
    }

    pub fn get_mut(&mut self, i: usize) -> &mut T {
        &mut self.data[i]
    }

    pub fn get(&self, i: usize) -> &T {
        &self.data[i]
    }
}

impl<T: Sized + Init, const N: usize> PerCpu<T, N> {
    pub fn init(&mut self) -> usize {
        let mut n = 0;
        for i in 0..N {
            if self.get_mut(i).init() {
                n += 1;
            }
        }
        n
    }
}

#[derive(Default, Debug)]
pub struct SmpStagedInit {
    stage: AtomicUsize,
}

impl SmpStagedInit {
    pub const fn new() -> Self {
        Self {
            stage: AtomicUsize::new(0),
        }
    }

    pub fn run(&self, stage: usize, only_core_0: bool, f: impl FnOnce() + 'static) {
        let id = arch::current_cpu_id();
        if !only_core_0 {
            f();
            if id != 0 {
                return;
            }
            self.stage.fetch_add(1, Ordering::Relaxed);
            return;
        }
        if id != 0 {
            loop {
                let val = self.stage.load(Ordering::Acquire);
                if val > stage {
                    return;
                }
                core::hint::spin_loop();
            }
        }
        f();
        self.stage.fetch_add(1, Ordering::Relaxed);
    }
}

#[inline(always)]
pub fn sideeffect() {
    unsafe { core::arch::asm!("") }
}

#[macro_export]
macro_rules! static_assert {
    ($condition:expr) => {
        // Based on the latest one in `rustc`'s one before it was [removed].
        //
        // [removed]: https://github.com/rust-lang/rust/commit/c2dad1c6b9f9636198d7c561b47a2974f5103f6d
        const _: () = [()][!($condition) as usize];
    };
}

#[derive(Debug)]
pub enum Storage {
    Alloc(*mut u8, Layout),
    Raw(*mut u8, usize),
}

impl Default for Storage {
    fn default() -> Self {
        Self::Raw(core::ptr::null_mut(), 0)
    }
}

impl Storage {
    #[inline]
    pub fn from_layout(layout: Layout) -> Self {
        let base = unsafe { alloc::alloc::alloc(layout) };
        Storage::Alloc(base, layout)
    }

    #[inline]
    pub fn from_raw(base: *mut u8, size: usize) -> Self {
        Storage::Raw(base, size)
    }

    #[inline]
    pub const fn new() -> Self {
        Storage::Raw(core::ptr::null_mut(), 0)
    }

    #[inline]
    pub fn base(&self) -> *mut u8 {
        match self {
            Storage::Alloc(base, _) => *base,
            Storage::Raw(base, _) => *base,
        }
    }

    #[inline]
    pub fn size(&self) -> usize {
        match self {
            Storage::Alloc(_, layout) => layout.size(),
            Storage::Raw(_, size) => *size,
        }
    }

    #[inline]
    pub fn as_slice(&self) -> &[u8] {
        unsafe { core::slice::from_raw_parts(self.base(), self.size()) }
    }

    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        unsafe { core::slice::from_raw_parts_mut(self.base(), self.size()) }
    }
}

impl Drop for Storage {
    #[inline]
    fn drop(&mut self) {
        if let Storage::Alloc(base, layout) = self {
            unsafe { alloc::alloc::dealloc(*base, *layout) }
        }
    }
}
