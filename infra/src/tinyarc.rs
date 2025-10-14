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

extern crate alloc;
use crate::{
    intrusive::Adapter,
    list::{
        typed_atomic_ilist::{
            AtomicListHead, AtomicListIterator as ListIterator,
            AtomicListReverseIterator as ListReverseIterator,
        },
        GenericList,
    },
};
use alloc::boxed::Box;
use core::{
    marker::PhantomData,
    ops::Deref,
    ptr::NonNull,
    sync::atomic::{fence, AtomicPtr, Ordering},
};

#[cfg(target_pointer_width = "32")]
type Uint = u8;
#[cfg(target_pointer_width = "32")]
type AtomicUint = core::sync::atomic::AtomicU8;

#[cfg(target_pointer_width = "64")]
type Uint = usize;
#[cfg(target_pointer_width = "64")]
type AtomicUint = core::sync::atomic::AtomicUsize;

#[derive(Debug)]
#[repr(C)]
pub struct TinyArcInner<T: Sized> {
    data: T,
    // We don't need a large counter as Arc, we don't have weak
    // counter either.
    rc: AtomicUint,
}

impl<T: Sized> TinyArcInner<T> {
    pub const fn const_new(data: T) -> Self {
        Self {
            data,
            rc: AtomicUint::new(1),
        }
    }

    pub const fn new(data: T) -> Self {
        Self::const_new(data)
    }
}

// We don't Send or Sync TinyArcInner directly. All TinyArcInner values should
// be static or allocated from the heap and wrapped in TinyArc.
unsafe impl<T> Send for TinyArcInner<T> {}
unsafe impl<T> Sync for TinyArcInner<T> {}

// Make it transparent so that we don't have extra space overhead when
// using Option<TinyArc<T>>.
// See https://rust-lang.github.io/unsafe-code-guidelines/layout/enums.html#discriminant-elision-on-option-like-enums.
// https://doc.rust-lang.org/nomicon/other-reprs.html#reprtransparent
#[derive(Debug)]
#[repr(transparent)]
pub struct TinyArc<T: Sized> {
    inner: NonNull<TinyArcInner<T>>,
}

impl<T: Default + Sized> Default for TinyArc<T> {
    fn default() -> Self {
        Self::new(T::default())
    }
}

impl<T> TinyArc<T> {
    #[inline]
    pub fn new(data: T) -> Self {
        let x = Box::new(TinyArcInner::const_new(data));
        assert_eq!(Box::as_ptr(&x) as usize % core::mem::align_of::<T>(), 0);
        Self {
            inner: unsafe { NonNull::new_unchecked(Box::into_raw(x)) },
        }
    }

    #[inline]
    pub const unsafe fn const_new(inner: &'static TinyArcInner<T>) -> Self {
        TinyArc {
            inner: NonNull::from_ref(inner),
        }
    }

    #[inline]
    pub unsafe fn from_inner(inner: NonNull<TinyArcInner<T>>) -> Self {
        inner.as_ref().rc.fetch_add(1, Ordering::Release);
        TinyArc { inner }
    }

    #[inline]
    pub fn get_handle(this: &Self) -> *const u8 {
        Self::as_ptr(this) as *const u8
    }

    #[inline]
    pub fn strong_count(this: &Self) -> usize {
        #[cfg(target_pointer_width = "32")]
        unsafe {
            this.inner.as_ref().rc.load(Ordering::Relaxed) as usize
        }
        #[cfg(target_pointer_width = "64")]
        unsafe {
            this.inner.as_ref().rc.load(Ordering::Relaxed)
        }
    }

    #[inline]
    pub unsafe fn increment_strong_count(this: &Self) {
        let old = this.inner.as_ref().rc.fetch_add(1, Ordering::Relaxed);
        assert_ne!(old, 0);
    }

    #[inline]
    pub unsafe fn decrement_strong_count(this: &Self) {
        let old = this.inner.as_ref().rc.fetch_sub(1, Ordering::Relaxed);
        assert_ne!(old, 1);
    }

    #[inline]
    pub fn is(this: &Self, that: &Self) -> bool {
        Self::get_handle(this) == Self::get_handle(that)
    }

    #[must_use]
    pub fn as_ptr(this: &Self) -> *const T {
        let ptr: *mut TinyArcInner<T> = NonNull::as_ptr(this.inner);

        // SAFETY: This cannot go through Deref::deref because this is required to retain raw/mut provenance
        unsafe { &raw mut (*ptr).data }
    }

    pub fn into_raw(this: Self) -> *const T {
        let ptr = Self::as_ptr(&this);
        core::mem::forget(this);
        ptr
    }

    pub unsafe fn from_raw(ptr: *const T) -> Self {
        // SAFETY: ptr offset is same as TinyArcInner struct offset no recalculation of
        // offset is required
        TinyArc {
            inner: NonNull::new_unchecked(ptr as *mut TinyArcInner<T>),
        }
    }

    // `get_mut` requires `&mut Arc` which is different from what Sync
    // indicates. Thus it's impossible to see two threads `get_mut` successfully
    // at the same time.
    pub fn get_mut(this: &mut Self) -> Option<&mut T> {
        let rc = unsafe { this.inner.as_ref().rc.load(Ordering::Acquire) };
        if rc != 1 {
            return None;
        }
        Some(unsafe { &mut this.inner.as_mut().data })
    }

    #[inline]
    pub unsafe fn get_mut_unchecked(this: &mut Self) -> &mut T {
        &mut this.inner.as_mut().data
    }

    #[inline]
    unsafe fn inner(this: &Self) -> &NonNull<TinyArcInner<T>> {
        &this.inner
    }

    #[inline]
    unsafe fn from_ptr(inner: *mut TinyArcInner<T>) -> Self {
        debug_assert!(!inner.is_null());
        TinyArc {
            inner: NonNull::new_unchecked(inner),
        }
    }
}

impl<T: Sized> Clone for TinyArc<T> {
    #[inline]
    fn clone(&self) -> TinyArc<T> {
        let old = unsafe { self.inner.as_ref() }
            .rc
            .fetch_add(1, Ordering::AcqRel);
        assert!(old >= 1);
        TinyArc { inner: self.inner }
    }
}

impl<T: Sized> Drop for TinyArc<T> {
    #[inline]
    fn drop(&mut self) {
        let old_val = unsafe { self.inner.as_ref() }
            .rc
            .fetch_sub(1, Ordering::Acquire);
        if old_val != 1 {
            return;
        }
        // Static data should never reach here.
        let x = unsafe { Box::from_non_null(self.inner) };
        drop(x);
    }
}

impl<T: Sized> Deref for TinyArc<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &T {
        unsafe { &self.inner.as_ref().data }
    }
}

// TinyArc doesn't contain the value it manages, but a pointer to the value. We
// also assume no alias of the internal NonNull, so it's safe to impl Send +
// Sync for it.
unsafe impl<T: Sized> Send for TinyArc<T> {}
unsafe impl<T: Sized> Sync for TinyArc<T> {}

// This list is semi-safe for concurrency. When performing list operations, the
// lock on the whole list must be acquired first. Must be noted, when detaching
// a node from a list, we must be sure that the node being detached exactly
// belongs to the list we are locking.
#[derive(Default, Debug)]
pub struct TinyArcList<T: Sized, A: Adapter> {
    head: AtomicListHead<T, A>,
    tail: AtomicListHead<T, A>,
}

impl<T: Sized, A: Adapter> TinyArcList<T, A> {
    pub const fn const_new() -> Self {
        Self {
            head: AtomicListHead::<T, A>::new(),
            tail: AtomicListHead::<T, A>::new(),
        }
    }

    pub const fn new() -> Self {
        Self::const_new()
    }

    #[inline]
    pub fn init(&mut self) -> bool {
        AtomicListHead::<T, A>::insert_after(&mut self.head, &mut self.tail)
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.head.next() == Some(NonNull::from_ref(&self.tail))
    }

    #[inline]
    pub fn list_head_of_mut(this: &mut TinyArc<T>) -> Option<&mut AtomicListHead<T, A>> {
        let this_val = TinyArc::<T>::get_mut(this)?;
        let ptr = this_val as *mut _ as *mut u8;
        let list_head_ptr = unsafe { ptr.add(A::offset()) as *mut AtomicListHead<T, A> };
        Some(unsafe { &mut *list_head_ptr })
    }

    #[inline]
    pub unsafe fn list_head_of_mut_unchecked(this: &mut TinyArc<T>) -> &mut AtomicListHead<T, A> {
        let this_val = TinyArc::<T>::get_mut_unchecked(this);
        let ptr = this_val as *mut _ as *mut u8;
        let list_head_ptr = ptr.add(A::offset()) as *mut AtomicListHead<T, A>;
        &mut *list_head_ptr
    }

    #[inline]
    pub unsafe fn make_arc_from(node: &AtomicListHead<T, A>) -> TinyArc<T> {
        let ptr = node as *const _ as *const u8;
        let mut offset = core::mem::offset_of!(TinyArcInner<T>, data);
        offset += A::offset();
        let inner = &*(ptr.sub(offset) as *const TinyArcInner<T>);
        TinyArc::from_inner(NonNull::from_ref(inner))
    }

    pub fn insert_after(other_node: &mut AtomicListHead<T, A>, mut me: TinyArc<T>) -> bool {
        let me_node = unsafe { Self::list_head_of_mut_unchecked(&mut me) };
        if !AtomicListHead::<T, A>::insert_after(other_node, me_node) {
            return false;
        }
        // The list shares ownership of me.
        core::mem::forget(me);
        true
    }

    pub fn insert_before(other_node: &mut AtomicListHead<T, A>, mut me: TinyArc<T>) -> bool {
        let me_node = unsafe { Self::list_head_of_mut_unchecked(&mut me) };
        if !AtomicListHead::<T, A>::insert_before(other_node, me_node) {
            return false;
        }
        // The list shares ownership of me.
        core::mem::forget(me);
        true
    }

    pub fn push_back(&mut self, me: TinyArc<T>) -> bool {
        if Self::insert_before(&mut self.tail, me) {
            return true;
        }
        false
    }

    pub fn back(&self) -> Option<TinyArc<T>> {
        if self.is_empty() {
            return None;
        }
        let Some(mut prev) = self.tail.prev() else {
            panic!("Tail's prev node should not be None");
        };
        Some(unsafe { Self::make_arc_from(prev.as_ref()) })
    }

    pub fn front(&self) -> Option<TinyArc<T>> {
        if self.is_empty() {
            return None;
        }
        let Some(mut next) = self.head.next() else {
            panic!("Head's next node should not be None");
        };
        Some(unsafe { Self::make_arc_from(next.as_ref()) })
    }

    pub fn pop_front(&mut self) -> Option<TinyArc<T>> {
        assert!(self.head.next().is_some());
        if self.is_empty() {
            return None;
        }
        let Some(mut next) = self.head.next() else {
            panic!("Head's next node should not be None");
        };
        let arc = unsafe { Self::make_arc_from(next.as_ref()) };
        let ok = AtomicListHead::<T, A>::detach(unsafe { next.as_mut() });
        assert!(ok);
        unsafe { TinyArc::<T>::decrement_strong_count(&arc) };
        Some(arc)
    }

    pub fn detach(me: &mut TinyArc<T>) -> bool {
        let me_node = unsafe { Self::list_head_of_mut_unchecked(me) };
        if !AtomicListHead::<T, A>::detach(me_node) {
            return false;
        }
        unsafe { TinyArc::<T>::decrement_strong_count(me) };
        true
    }

    pub fn clear(&mut self) -> usize {
        let mut c = 0;
        for mut i in
            TinyArcListIterator::<T, A>::new(&self.head, Some(NonNull::from_ref(&self.tail)))
        {
            Self::detach(&mut i);
            c += 1;
        }
        c
    }

    pub fn iter(&self) -> TinyArcListIterator<T, A> {
        TinyArcListIterator::<T, A>::new(&self.head, Some(NonNull::from_ref(&self.tail)))
    }

    // Find a stable sorting position.
    fn find_insert_position_by<Compare>(
        compare: Compare,
        it: TinyArcListIterator<T, A>,
        val: &TinyArc<T>,
    ) -> Option<TinyArc<T>>
    where
        Compare: Fn(&T, &T) -> core::cmp::Ordering,
    {
        use core::cmp::Ordering;
        let mut last = None;
        for other_val in it {
            let ord = compare(val, &other_val);
            if ord == Ordering::Less {
                return last;
            }
            last = Some(other_val);
        }
        last
    }

    // Sort by ascending order.
    #[inline]
    pub fn insert_by<Compare>(
        compare: Compare,
        head: &mut AtomicListHead<T, A>,
        val: TinyArc<T>,
    ) -> bool
    where
        Compare: Fn(&T, &T) -> core::cmp::Ordering,
    {
        let Some(mut other_val) =
            Self::find_insert_position_by(compare, TinyArcListIterator::new(head, None), &val)
        else {
            return Self::insert_after(head, val);
        };
        Self::insert_after(
            unsafe { Self::list_head_of_mut_unchecked(&mut other_val) },
            val,
        )
    }

    pub fn push_by<Compare>(&mut self, compare: Compare, val: TinyArc<T>) -> bool
    where
        Compare: Fn(&T, &T) -> core::cmp::Ordering,
    {
        let Some(mut other_val) = Self::find_insert_position_by(
            compare,
            TinyArcListIterator::new(&self.head, Some(NonNull::from_ref(&self.tail))),
            &val,
        ) else {
            return Self::insert_after(&mut self.head, val);
        };
        Self::insert_after(
            unsafe { Self::list_head_of_mut_unchecked(&mut other_val) },
            val,
        )
    }
}

impl<T: Sized, A: Adapter> Drop for TinyArcList<T, A> {
    #[inline]
    fn drop(&mut self) {
        // NOTE: Elements should be cleared by calling `clear` method
        // since move occurs when dropping. Do you recall how drop is
        // called? It's `drop(val)`.
        // Maybe we can change `head` and `tail` to `Box<struct(AtomicListHead,AtomicListHead)>`,
        // which is implicitly pinned.
    }
}

impl<T: Sized, A: Adapter> GenericList for TinyArcList<T, A> {
    type Node = AtomicListHead<T, A>;
}

pub struct TinyArcListIterator<T, A: Adapter> {
    it: ListIterator<T, A>,
}

pub struct TinyArcListReverseIterator<T, A: Adapter> {
    it: ListReverseIterator<T, A>,
}

impl<T, A: Adapter> TinyArcListIterator<T, A> {
    pub fn new(head: &AtomicListHead<T, A>, tail: Option<NonNull<AtomicListHead<T, A>>>) -> Self {
        Self {
            it: ListIterator::new(head, tail),
        }
    }
}

impl<T, A: Adapter> TinyArcListReverseIterator<T, A> {
    pub fn new(tail: &AtomicListHead<T, A>, head: Option<NonNull<AtomicListHead<T, A>>>) -> Self {
        Self {
            it: ListReverseIterator::new(tail, head),
        }
    }
}

impl<T, A: Adapter> Iterator for TinyArcListIterator<T, A> {
    type Item = TinyArc<T>;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.it.next()?;
        Some(unsafe { TinyArcList::<T, A>::make_arc_from(node.as_ref()) })
    }
}

impl<T, A: Adapter> Iterator for TinyArcListReverseIterator<T, A> {
    type Item = TinyArc<T>;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.it.next()?;
        Some(unsafe { TinyArcList::<T, A>::make_arc_from(node.as_ref()) })
    }
}

#[repr(transparent)]
#[derive(Debug, Default)]
pub struct TinyArcCas<T: Sized> {
    inner: Option<TinyArc<T>>,
}

impl<T: Sized> Clone for TinyArcCas<T> {
    fn clone(&self) -> Self {
        Self {
            inner: self.load(Ordering::Relaxed),
        }
    }
}

impl<T: Sized> TinyArcCas<T> {
    #[inline]
    fn as_mut_ptr(this: &Option<TinyArc<T>>) -> *mut TinyArcInner<T> {
        this.as_ref().map_or(core::ptr::null_mut(), |v| unsafe {
            (*TinyArc::inner(v)).as_ptr()
        })
    }

    pub fn load(&self, order: Ordering) -> Option<TinyArc<T>> {
        let this = unsafe { &*(self as *const Self as *const AtomicPtr<TinyArcInner<T>>) };
        let inner = this.load(order);
        if inner.is_null() {
            return None;
        }
        Some(unsafe { TinyArc::from_inner(NonNull::new_unchecked(inner)) })
    }

    pub fn from_arc(arc: TinyArc<T>) -> Self {
        Self { inner: Some(arc) }
    }

    pub const fn new(inner: Option<TinyArc<T>>) -> Self {
        Self { inner }
    }

    // Why don't we use standard interface? Like
    // ```
    //     pub fn compare_exchange(
    //         &self,
    //         compare: Option<TinyArc<T>>,
    //         new: Option<TinyArc<T>>,
    //         success: Ordering,
    //         failure: Ordering,
    //     ) -> Result<Option<TinyArc<T>>, Option<TinyArc<T>>
    //  ```
    //
    // When we are on the error path, like
    // ```
    //        match this.compare_exchange(compare_ptr, new_ptr, success, failure) {
    //            Ok(_) => { ... }
    //            // We are unable to determine if addr is still valid at this point,
    //            // so we can't return an Option<TinyArc> on error.
    //            Err(addr) => { ... }
    //        }
    // ```

    // Return true if CAS is performed successfully.
    pub fn cas(
        &self,
        compare: Option<TinyArc<T>>,
        new: Option<TinyArc<T>>,
        success: Ordering,
        failure: Ordering,
    ) -> bool {
        let this = unsafe { &*(self as *const Self as *const AtomicPtr<TinyArcInner<T>>) };
        let compare_ptr = Self::as_mut_ptr(&compare);
        let new_ptr = Self::as_mut_ptr(&new);
        // Must be noted, counters of these TinyArc are not updated atomically.
        match this.compare_exchange(compare_ptr, new_ptr, success, failure) {
            Ok(_) => {
                if let Some(compare) = compare.as_ref() {
                    unsafe { TinyArc::decrement_strong_count(compare) };
                }
                core::mem::forget(new);
                true
            }
            Err(_) => false,
        }
    }

    pub fn swap(&self, new: Option<TinyArc<T>>, order: Ordering) -> Option<TinyArc<T>> {
        let this = unsafe { &*(self as *const Self as *const AtomicPtr<TinyArcInner<T>>) };
        let new_ptr = Self::as_mut_ptr(&new);
        let old_ptr = this.swap(new_ptr, order);
        core::mem::forget(new);
        if old_ptr.is_null() {
            return None;
        }
        // old_ptr must be a valid *mut TinyArcInner<T>, we can use it to
        // recover a TinyArc<T>.
        Some(unsafe { TinyArc::from_ptr(old_ptr) })
    }
}

#[cfg(test)]
mod tests {
    extern crate test;
    use super::*;
    use crate::{
        impl_simple_intrusive_adapter, list::typed_atomic_ilist::AtomicListHead, tinyrwlock::RwLock,
    };
    use test::Bencher;

    impl_simple_intrusive_adapter!(OffsetOfCsl, Thread, control_status_list);
    impl_simple_intrusive_adapter!(OffsetOfTl, Thread, timer_list);

    type ControlStatusList = TinyArcList<Thread, OffsetOfCsl>;
    type TimerList = TinyArcList<Thread, OffsetOfTl>;

    #[derive(Default, Debug)]
    pub struct Thread {
        pub control_status_list: <ControlStatusList as GenericList>::Node,
        pub timer_list: <TimerList as GenericList>::Node,
        pub id: usize,
        pub prio: usize,
    }

    impl Thread {
        pub fn new(id: usize) -> Self {
            Self {
                id,
                ..Default::default()
            }
        }
    }

    #[test]
    fn test_basic() {
        let mut t = TinyArc::new(Thread::default());
        assert_eq!(&t.control_status_list as *const _, unsafe {
            ControlStatusList::list_head_of_mut_unchecked(&mut t)
        } as *const _,);
        assert_eq!(&t.timer_list as *const _, unsafe {
            TimerList::list_head_of_mut_unchecked(&mut t)
        } as *const _,);
    }

    #[test]
    fn test_get_mut() {
        let mut t = TinyArc::new(0);
        let _clone1 = t.clone();
        assert!(TinyArc::<_>::get_mut(&mut t).is_none());
    }

    #[test]
    fn test_detach_during_iter() {
        type L = <ControlStatusList as GenericList>::Node;
        let mut head = RwLock::new(L::default());
        let mut w = head.write();
        let t = TinyArc::new(Thread::default());
        ControlStatusList::insert_after(&mut *w, t);
        for mut e in TinyArcListIterator::new(&*w, None) {
            ControlStatusList::detach(&mut e);
        }
    }

    #[test]
    fn test_insert_after_false() {
        type L = <ControlStatusList as GenericList>::Node;
        let mut head = L::default();
        let mut t = TinyArc::new(Thread::new(1));
        unsafe {
            let mut head2 = ControlStatusList::list_head_of_mut_unchecked(&mut t);
            AtomicListHead::insert_before(&mut head, head2);
        }

        let result = ControlStatusList::insert_after(&mut head, t);

        assert!(!result);
    }

    #[test]
    fn test_push_back_false() {
        type L = <ControlStatusList as GenericList>::Node;
        let mut l = ControlStatusList::default();
        l.init();

        let mut head = L::default();
        let mut t = TinyArc::new(Thread::new(1));
        unsafe {
            let mut head2 = ControlStatusList::list_head_of_mut_unchecked(&mut t);
            AtomicListHead::insert_before(&mut head, head2);
        }

        let result = ControlStatusList::push_back(&mut l, t);

        assert!(!result);
    }

    #[test]
    fn test_insert_and_detach() {
        type L = <ControlStatusList as GenericList>::Node;
        let n = 4;
        let mut head = L::default();
        for i in 0..n {
            let t = TinyArc::new(Thread::new(i));
            assert_eq!(TinyArc::strong_count(&t), 1);
            ControlStatusList::insert_after(&mut head, t.clone());
            assert_eq!(TinyArc::strong_count(&t), 2);
        }
        let mut counter = (n - 1) as isize;
        for mut i in TinyArcListIterator::new(&head, None) {
            assert_eq!(i.id, counter as usize);
            assert_eq!(TinyArc::strong_count(&i), 2);
            counter -= 1;
            assert!(ControlStatusList::detach(&mut i));
            assert_eq!(TinyArc::strong_count(&i), 1);
        }
    }

    #[test]
    fn test_insert_before_and_detach() {
        type L = <ControlStatusList as GenericList>::Node;
        let n = 4;
        let mut tail = L::default();
        for i in 0..n {
            let t = TinyArc::new(Thread::new(i));
            assert_eq!(TinyArc::strong_count(&t), 1);
            ControlStatusList::insert_before(&mut tail, t.clone());
            assert_eq!(TinyArc::strong_count(&t), 2);
        }
        let mut counter = (n - 1) as isize;
        for mut i in TinyArcListReverseIterator::new(&tail, None) {
            assert_eq!(i.id, counter as usize);
            assert_eq!(TinyArc::strong_count(&i), 2);
            counter -= 1;
            assert!(ControlStatusList::detach(&mut i));
            assert_eq!(TinyArc::strong_count(&i), 1);
        }
    }

    #[test]
    fn test_push_and_pop() {
        type L = <ControlStatusList as GenericList>::Node;
        let n = 16;
        let mut l = ControlStatusList::default();
        l.init();
        for i in 0..n {
            let mut t = TinyArc::new(Thread::new(i));
            assert_eq!(TinyArc::strong_count(&t), 1);
            let node = unsafe { ControlStatusList::list_head_of_mut_unchecked(&mut t) };
            assert!(node.is_detached());
            assert!(l.push_back(t.clone()));
            assert!(!ControlStatusList::insert_before(&mut l.tail, t.clone()));
            assert_eq!(TinyArc::strong_count(&t), 2);
        }
        for i in 0..n {
            let t = l.pop_front();
            assert!(t.is_some());
            let t = unsafe { t.unwrap_unchecked() };
            assert_eq!(t.id, i);
            assert_eq!(TinyArc::strong_count(&t), 1);
        }
        assert!(l.pop_front().is_none());
        assert!(l.is_empty());
    }

    #[test]
    fn test_push_and_drop() {
        type L = <ControlStatusList as GenericList>::Node;
        let n = 16;
        let mut l = ControlStatusList::default();
        l.init();
        for i in 0..n {
            let mut t = TinyArc::new(Thread::new(i));
            assert_eq!(TinyArc::strong_count(&t), 1);
            let node = unsafe { ControlStatusList::list_head_of_mut_unchecked(&mut t) };
            assert!(node.is_detached());
            assert!(l.push_back(t.clone()));
            assert!(!ControlStatusList::insert_before(&mut l.tail, t.clone()));
            assert_eq!(TinyArc::strong_count(&t), 2);
        }
        l.clear();
    }

    #[test]
    fn test_detach_during_iter_2() {
        type L = <ControlStatusList as GenericList>::Node;
        let mut l = ControlStatusList::default();
        l.init();
        let mut n = 16;
        for i in 0..n {
            let t = TinyArc::new(Thread::new(i));
            assert_eq!(TinyArc::strong_count(&t), 1);
            assert!(l.push_back(t.clone()));
        }

        loop {
            let mut iter = l.iter();
            if let Some(mut t) = iter.next() {
                assert_eq!(TinyArc::strong_count(&t), 2);
                assert!(ControlStatusList::detach(&mut t));
                assert_eq!(TinyArc::strong_count(&t), 1);
                n -= 1;
            } else {
                break;
            }
        }
        assert_eq!(n, 0);
    }

    #[test]
    fn test_detach_and_insert_during_iter() {
        type L = <ControlStatusList as GenericList>::Node;
        let mut l = ControlStatusList::default();
        l.init();
        let n = 16;
        for i in 0..n {
            let mut t = TinyArc::new(Thread::new(i));
            assert_eq!(TinyArc::strong_count(&t), 1);
            let node = unsafe { ControlStatusList::list_head_of_mut_unchecked(&mut t) };
            assert!(node.is_detached());
            assert!(l.push_back(t.clone()));
        }

        for i in 0..n {
            let mut iter = l.iter();
            if let Some(mut t) = iter.next() {
                assert_eq!(TinyArc::strong_count(&t), 2);
                assert!(ControlStatusList::detach(&mut t));
                assert_eq!(TinyArc::strong_count(&t), 1);
                // insert back to the list again
                l.push_back(t.clone());
            }
        }
        l.clear();
    }

    #[test]
    fn test_into_raw_and_from_raw() {
        let t = TinyArc::new(Thread::default());
        assert_eq!(TinyArc::strong_count(&t), 1);
        let ptr = TinyArc::into_raw(t);
        let t2 = unsafe { TinyArc::from_raw(ptr) };
        assert_eq!(TinyArc::strong_count(&t2), 1);
    }

    #[bench]
    fn bench_insert_and_detach(b: &mut Bencher) {
        type L = <ControlStatusList as GenericList>::Node;
        let n = 1 << 16;
        b.iter(|| {
            let mut head = L::default();
            let mut tail = L::default();
            L::insert_after(&mut head, &mut tail);
            for i in 0..n {
                let mut t = TinyArc::new(Thread::new(i));
                assert_eq!(TinyArc::strong_count(&t), 1);
                ControlStatusList::insert_after(&mut head, t.clone());
                assert_eq!(TinyArc::strong_count(&t), 2);
            }
            let mut counter = (n - 1) as isize;
            for mut i in TinyArcListIterator::new(&head, Some(NonNull::from_ref(&tail))) {
                assert_eq!(i.id, counter as usize);
                assert_eq!(TinyArc::strong_count(&i), 2);
                counter -= 1;
                assert!(ControlStatusList::detach(&mut i));
                assert_eq!(TinyArc::strong_count(&i), 1);
            }
        });
    }

    #[bench]
    fn bench_insert_and_detach_1(b: &mut Bencher) {
        let n = 1 << 16;
        b.iter(|| {
            type L = <ControlStatusList as GenericList>::Node;
            let mut head = L::default();
            for i in 0..n {
                ControlStatusList::insert_after(&mut head, TinyArc::new(Thread::new(i)));
            }
            for mut i in TinyArcListIterator::new(&head, None) {
                ControlStatusList::detach(&mut i);
            }
        });
    }

    #[bench]
    fn bench_insert_and_detach_1_std(b: &mut Bencher) {
        use alloc::{collections::linked_list::LinkedList, sync::Arc};
        let n = 1 << 16;
        b.iter(|| {
            let mut mu = spin::Mutex::new(LinkedList::new());
            for i in 0..n {
                let Some(mut guard) = mu.try_lock() else {
                    continue;
                };
                guard.push_back(Arc::new(Thread::new(i)));
            }
            for i in 0..n {
                let Some(mut guard) = mu.try_lock() else {
                    continue;
                };
                guard.pop_front();
            }
        });
    }

    // When a Thread belongs to two lists.
    #[bench]
    fn bench_insert_and_detach_2(b: &mut Bencher) {
        type Csl = <ControlStatusList as GenericList>::Node;
        type Tl = <TimerList as GenericList>::Node;
        let n = 1 << 16;
        b.iter(|| {
            let mut csl_head = Csl::default();
            let mut tl_head = Tl::default();
            for i in 0..n {
                let t = TinyArc::new(Thread::new(i));
                ControlStatusList::insert_after(&mut csl_head, t.clone());
                TimerList::insert_after(&mut tl_head, t);
            }
            for mut i in TinyArcListIterator::new(&csl_head, None) {
                ControlStatusList::detach(&mut i);
            }
            for mut i in TinyArcListIterator::new(&tl_head, None) {
                TimerList::detach(&mut i);
            }
        });
    }

    // When a Thread belongs to two lists.
    #[bench]
    fn bench_insert_and_detach_2_std(b: &mut Bencher) {
        use alloc::{collections::linked_list::LinkedList, sync::Arc};
        let n = 1 << 16;
        b.iter(|| {
            let mut l0 = spin::Mutex::new(LinkedList::new());
            let mut l1 = spin::Mutex::new(LinkedList::new());
            for i in 0..n {
                let t = Arc::new(Thread::new(i));
                let Some(mut g0) = l0.try_lock() else {
                    continue;
                };
                g0.push_back(t.clone());
                let Some(mut g1) = l1.try_lock() else {
                    continue;
                };
                g1.push_back(t);
            }
            for i in 0..n {
                let Some(mut g0) = l0.try_lock() else {
                    continue;
                };
                g0.pop_front();
            }
            for i in 0..n {
                let Some(mut g1) = l1.try_lock() else {
                    continue;
                };
                g1.pop_front();
            }
        });
    }

    #[test]
    fn insert_by_prio() {
        let mut head = <ControlStatusList as GenericList>::Node::new();
        let mut t0 = TinyArc::new(Thread::new(0));
        TinyArc::get_mut(&mut t0).unwrap().prio = 2;
        let mut t1 = TinyArc::new(Thread::new(1));
        TinyArc::get_mut(&mut t1).unwrap().prio = 0;
        let mut t2 = TinyArc::new(Thread::new(2));
        TinyArc::get_mut(&mut t2).unwrap().prio = 1;
        let mut t3 = TinyArc::new(Thread::new(3));
        TinyArc::get_mut(&mut t3).unwrap().prio = 0;
        let cmp_prio = |l: &Thread, r: &Thread| l.prio.cmp(&r.prio);
        let ok = ControlStatusList::insert_by(cmp_prio, &mut head, t0.clone());
        assert!(ok);
        let ok = ControlStatusList::insert_by(cmp_prio, &mut head, t1.clone());
        assert!(ok);
        let ok = ControlStatusList::insert_by(cmp_prio, &mut head, t2.clone());
        assert!(ok);
        let ok = ControlStatusList::insert_by(cmp_prio, &mut head, t3.clone());
        assert!(ok);
        // We expect the list is sorted as {t1, t3, t2, t0}.
        let mut it = TinyArcListIterator::new(&head, None);
        let mut fst = it.next().unwrap();
        assert_eq!(TinyArc::as_ptr(&fst), TinyArc::as_ptr(&t1));
        let ok = ControlStatusList::detach(&mut fst);
        assert!(ok);
        let mut sec = it.next().unwrap();
        assert_eq!(TinyArc::as_ptr(&sec), TinyArc::as_ptr(&t3));
        let ok = ControlStatusList::detach(&mut sec);
        assert!(ok);
        let mut third = it.next().unwrap();
        assert_eq!(TinyArc::as_ptr(&third), TinyArc::as_ptr(&t2));
        let ok = ControlStatusList::detach(&mut third);
        assert!(ok);
        let mut fourth = it.next().unwrap();
        assert_eq!(TinyArc::as_ptr(&fourth), TinyArc::as_ptr(&t0));
        let ok = ControlStatusList::detach(&mut fourth);
        assert!(ok);
    }

    #[test]
    fn test_arc_cas_basic() {
        let t = TinyArc::new(42);
        let cas = TinyArcCas::default();
        assert!(cas.cas(None, Some(t.clone()), Ordering::SeqCst, Ordering::Relaxed));
        assert!(TinyArc::is(&cas.load(Ordering::Relaxed).unwrap(), &t));
        // 2 owners: t, cas
        assert_eq!(TinyArc::strong_count(&t), 2);
        assert!(!cas.cas(None, Some(t.clone()), Ordering::SeqCst, Ordering::Relaxed));
        // 2 owners: t, cas
        assert_eq!(TinyArc::strong_count(&t), 2);
        let s = TinyArc::new(43);
        // 1 owners: s
        assert_eq!(TinyArc::strong_count(&s), 1);
        assert!(cas.cas(
            Some(t.clone()),
            Some(s.clone()),
            Ordering::SeqCst,
            Ordering::Relaxed,
        ));
        // 2 owners: s, cas.
        assert_eq!(TinyArc::strong_count(&s), 2);
        assert!(TinyArc::is(&cas.load(Ordering::Relaxed).unwrap(), &s));
        // 1 owner: t
        assert_eq!(TinyArc::strong_count(&t), 1);
        assert!(cas.cas(Some(s.clone()), None, Ordering::SeqCst, Ordering::Relaxed));
        assert_eq!(TinyArc::strong_count(&s), 1);
    }

    #[test]
    fn test_swap_basic() {
        let cas = TinyArcCas::default();
        let t = TinyArc::new(42);
        let old = cas.swap(Some(t.clone()), Ordering::SeqCst);
        assert!(old.is_none());
        assert_eq!(TinyArc::strong_count(&t), 2);
        let old = cas.swap(old, Ordering::SeqCst);
        assert!(TinyArc::is(&old.unwrap(), &t));
        assert_eq!(TinyArc::strong_count(&t), 1);
    }

    #[test]
    fn test_swap_no_none() {
        let cas = TinyArcCas::from_arc(TinyArc::new(42));
        let s = TinyArc::new(43);
        let old = cas.swap(Some(s.clone()), Ordering::SeqCst);
        assert!(old.is_some());
        assert_eq!(TinyArc::strong_count(old.as_ref().unwrap()), 1);
        assert_eq!(TinyArc::strong_count(&s), 2);
        assert_eq!(*old.unwrap(), 42);
        let old = cas.swap(None, Ordering::SeqCst);
        assert!(old.is_some());
        assert_eq!(*old.unwrap(), 43);
        assert_eq!(TinyArc::strong_count(&s), 1);
    }
}
