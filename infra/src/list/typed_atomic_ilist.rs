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

use crate::intrusive::Adapter;
use core::{
    marker::PhantomData,
    ptr::NonNull,
    sync::atomic::{AtomicPtr, AtomicUsize, Ordering},
};

// `prev` is a tagged pointer. https://doc.rust-lang.org/std/sync/atomic/struct.AtomicPtr.html#method.fetch_or
// shows what tagged pointer means.
// We use "C" ABI memory layout here, so that this type's alignment is at least
// the same as AtomicPtr, so that we can use the least significant bit to
// indicate if a list operation is ongoing.
#[repr(C)]
#[derive(Default, Debug)]
pub struct AtomicListHead<T: Sized, A: Adapter> {
    prev: AtomicPtr<AtomicListHead<T, A>>,
    next: Option<NonNull<AtomicListHead<T, A>>>,
    _t: PhantomData<T>,
    _a: PhantomData<A>,
}

impl<T, A: Adapter> AtomicListHead<T, A> {
    #[inline]
    pub const fn new() -> Self {
        Self {
            prev: AtomicPtr::new(core::ptr::null_mut()),
            next: None,
            _t: PhantomData,
            _a: PhantomData,
        }
    }

    #[inline]
    fn try_lock(&self) -> bool {
        let old_val = self.prev.fetch_or(1, Ordering::Acquire);
        old_val.addr() & 1 == 0
    }

    #[inline]
    fn unlock(&self) {
        self.prev.fetch_and(!1, Ordering::Release);
    }

    #[inline]
    pub fn owner(&self) -> &T {
        let ptr = self as *const _ as *const u8;
        let base = unsafe { ptr.sub(A::offset()) as *const T };
        unsafe { &*base }
    }

    #[inline]
    pub unsafe fn owner_mut(&mut self) -> &mut T {
        let ptr = self as *mut _ as *mut u8;
        let base = unsafe { ptr.sub(A::offset()) as *mut T };
        unsafe { &mut *base }
    }

    #[inline]
    pub unsafe fn list_head_of_mut_unchecked(this: &mut T) -> &mut Self {
        let ptr = this as *mut _ as *mut u8;
        let list_head_ptr = ptr.add(A::offset()) as *mut Self;
        &mut *list_head_ptr
    }

    #[inline]
    pub fn prev(&self) -> Option<NonNull<Self>> {
        NonNull::new(self.prev_ptr())
    }

    #[inline]
    fn prev_ptr(&self) -> *mut Self {
        let tagged = self.prev.load(Ordering::Relaxed);
        tagged.map_addr(|p| p & !1)
    }

    #[inline]
    fn next_ptr(&self) -> *mut Self {
        self.next.map_or(core::ptr::null_mut(), |v| v.as_ptr())
    }

    #[inline]
    pub fn next(&self) -> Option<NonNull<Self>> {
        self.next
    }

    #[inline]
    pub fn is_detached(&self) -> bool {
        self.prev().is_none() && self.next().is_none()
    }

    // For our use scenarios, we only have to lock `me`. The whole list is
    // expected to be protected by a spin lock.
    pub fn insert_after(head: &mut Self, me: &mut Self) -> bool {
        let locked = me.try_lock();
        if !locked {
            return false;
        }
        if !me.is_detached() {
            me.unlock();
            return false;
        }
        let next = core::mem::replace(&mut head.next, Some(NonNull::from_mut(me)));
        me.next = next;
        let prev = next.map_or(Some(NonNull::from_mut(head)), |mut v| {
            let old = unsafe { v.as_mut().prev.swap(me as *mut _, Ordering::Relaxed) };
            debug_assert_eq!(old, head as *mut _);
            NonNull::new(old)
        });
        // Unlock simultaneously.
        me.prev.store(
            prev.map_or(core::ptr::null_mut(), |v| v.as_ptr()),
            Ordering::Release,
        );
        true
    }

    pub fn insert_before(tail: &mut Self, me: &mut Self) -> bool {
        let locked = me.try_lock();
        if !locked {
            return false;
        }
        if !me.is_detached() {
            me.unlock();
            return false;
        }
        let mut prev = NonNull::new(tail.prev.swap(me as *mut _, Ordering::Relaxed));
        if let Some(mut v) = prev.as_mut() {
            unsafe { v.as_mut().next = Some(NonNull::from_mut(me)) };
        };
        me.next = Some(NonNull::from_mut(tail));
        // Unlock simultaneously.
        me.prev.store(
            prev.map_or(core::ptr::null_mut(), |v| v.as_ptr()),
            Ordering::Release,
        );
        true
    }

    // When we are detaching the node, we must know clearly which list the node belongs to.
    pub fn detach(me: &mut Self) -> bool {
        let locked = me.try_lock();
        if !locked {
            return false;
        }
        if me.is_detached() {
            me.unlock();
            return false;
        }
        let prev_ptr = me.prev_ptr();
        let mut prev = NonNull::new(prev_ptr);
        if let Some(mut v) = prev.as_mut() {
            unsafe { v.as_mut().next = me.next };
        };
        if let Some(mut next) = me.next {
            unsafe { next.as_mut().prev.store(prev_ptr, Ordering::Relaxed) };
        };
        me.next = None;
        // Unlock simultaneously.
        me.prev.store(core::ptr::null_mut(), Ordering::Release);
        true
    }
}

unsafe impl<T, A: crate::intrusive::Adapter> Sync for AtomicListHead<T, A> {}
impl<T, A> !Send for AtomicListHead<T, A> {}

pub struct AtomicListIterator<T, A: Adapter> {
    next: Option<NonNull<AtomicListHead<T, A>>>,
    tail: Option<NonNull<AtomicListHead<T, A>>>,
}

impl<T, A: Adapter> AtomicListIterator<T, A> {
    pub fn new(head: &AtomicListHead<T, A>, tail: Option<NonNull<AtomicListHead<T, A>>>) -> Self {
        Self {
            next: head.next,
            tail,
        }
    }
}

impl<T, A: Adapter> Iterator for AtomicListIterator<T, A> {
    type Item = NonNull<AtomicListHead<T, A>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.next == self.tail {
            return None;
        }
        // FIXME: Shall we unwrap_unchecked directly?
        let Some(current) = self.next else {
            panic!("Tail node is specified, but encountered None during iteration");
        };
        self.next = unsafe { current.as_ref().next };
        Some(current)
    }
}

pub struct AtomicListReverseIterator<T, A: Adapter> {
    prev: *mut AtomicListHead<T, A>,
    head: *mut AtomicListHead<T, A>,
}

impl<T, A: Adapter> AtomicListReverseIterator<T, A> {
    pub fn new(tail: &AtomicListHead<T, A>, head: Option<NonNull<AtomicListHead<T, A>>>) -> Self {
        Self {
            prev: tail.prev_ptr(),
            head: head.map_or(core::ptr::null_mut(), |v| v.as_ptr()),
        }
    }
}

impl<T, A: Adapter> Iterator for AtomicListReverseIterator<T, A> {
    type Item = NonNull<AtomicListHead<T, A>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.prev == self.head {
            return None;
        }
        let current = NonNull::new(self.prev);
        self.prev = unsafe { (*self.prev).prev_ptr() };
        current
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{tinyarc::TinyArc as Arc, tinyrwlock::RwLock};
    use core::mem::offset_of;
    use std::thread;

    #[derive(Default, Debug)]
    struct OffsetOfLh;

    impl const Adapter for OffsetOfLh {
        #[inline]
        fn offset() -> usize {
            offset_of!(Foo, lh)
        }
    }

    #[derive(Default, Debug)]
    pub struct Foo {
        head: [u8; 8],
        lh: AtomicListHead<Foo, OffsetOfLh>,
        tail: [u8; 8],
        id: usize,
    }

    #[test]
    fn test_basic() {
        let f = Foo::default();
        let t = &f.lh;
        let g = t.owner();
        assert_eq!(&f as *const _, g as *const _);
        assert!(t.try_lock());
        assert!(!t.try_lock());
        assert!(!t.try_lock());
        t.unlock();
        assert!(t.try_lock());
        assert!(!t.try_lock());
        assert!(!t.try_lock());
    }

    #[test]
    fn test_insert_and_detach() {
        type Ty = AtomicListHead<Foo, OffsetOfLh>;
        let mut a = Foo::default();
        assert!(a.lh.is_detached());
        let mut b = Foo::default();
        let mut c = Foo::default();
        assert!(b.lh.is_detached());
        assert!(Ty::insert_after(&mut a.lh, &mut b.lh));
        assert!(!a.lh.is_detached());
        assert!(!b.lh.is_detached());
        Ty::detach(&mut b.lh);
        assert!(a.lh.is_detached());
        assert!(a.lh.prev_ptr().is_null());
        assert!(b.lh.is_detached());
        assert!(b.lh.prev_ptr().is_null());
        assert!(Ty::insert_after(&mut a.lh, &mut c.lh));
        assert!(b.lh.try_lock());
        assert!(!Ty::insert_before(&mut a.lh, &mut b.lh));
        b.lh.unlock();
        assert!(Ty::insert_before(&mut a.lh, &mut b.lh));
        assert_eq!(a.lh.prev_ptr(), &mut b.lh as *mut _);
        assert_eq!(a.lh.next_ptr(), &mut c.lh as *mut _);
        assert_eq!(c.lh.prev_ptr(), &mut a.lh as *mut _);
        assert_eq!(c.lh.next_ptr(), core::ptr::null_mut());
        assert_eq!(b.lh.prev_ptr(), core::ptr::null_mut());
        assert_eq!(b.lh.next_ptr(), &mut a.lh as *mut _);
        assert!(b.lh.try_lock());
        assert!(!b.lh.try_lock());
        b.lh.unlock();
        assert!(Ty::detach(&mut a.lh));
        assert!(!Ty::detach(&mut a.lh));
        assert!(a.lh.try_lock());
        assert!(!Ty::insert_after(&mut c.lh, &mut a.lh));
        a.lh.unlock();
        assert!(Ty::insert_after(&mut c.lh, &mut a.lh));
        assert!(!a.lh.is_detached());
        assert!(!b.lh.is_detached());
        assert!(!c.lh.is_detached());
    }

    #[test]
    fn test_concurrent_ops() {
        type Ty = AtomicListHead<Foo, OffsetOfLh>;
        let head = Arc::new(RwLock::new(Ty::new()));
        let n = 1024;
        let mut vt = Vec::new();
        for i in 0..n {
            let head = head.clone();
            let t = thread::spawn(move || {
                let mut f = Foo::default();
                for k in 0..128 {
                    {
                        let mut h = head.write();
                        assert!(Ty::insert_after(&mut *h, &mut f.lh));
                    }
                    {
                        let mut h = head.write();
                        assert!(Ty::detach(&mut f.lh));
                        assert!(f.lh.is_detached());
                    }
                }
            });
            vt.push(t);
        }
        for t in vt {
            t.join().unwrap();
        }
    }

    #[test]
    fn test_concurrent_ops1() {
        type Ty = AtomicListHead<Foo, OffsetOfLh>;
        let head = Arc::new(RwLock::new(Ty::new()));
        let t = Arc::new(Foo::default());
        let inserted = Arc::new(AtomicUsize::new(0));
        let detached = Arc::new(AtomicUsize::new(0));
        let n = 1024;
        let mut vt = Vec::new();
        for i in 0..n {
            let head = head.clone();
            let mut f = t.clone();
            let inserted = inserted.clone();
            let detached = detached.clone();
            let t = thread::spawn(move || {
                let lh = unsafe {
                    Ty::list_head_of_mut_unchecked(Arc::<Foo>::get_mut_unchecked(&mut f))
                };
                for k in 0..256 {
                    {
                        let mut h = head.write();
                        if Ty::insert_after(&mut *h, lh) {
                            inserted.fetch_add(1, Ordering::Relaxed);
                        }
                        if Ty::detach(lh) {
                            detached.fetch_add(1, Ordering::Relaxed);
                        }
                    }
                }
            });
            vt.push(t);
        }
        for t in vt {
            t.join().unwrap();
        }
        let inserted = inserted.load(Ordering::Relaxed);
        let detached = detached.load(Ordering::Relaxed);
        assert_eq!(inserted, detached);
    }

    #[test]
    fn test_concurrent_ops2() {
        type Ty = AtomicListHead<Foo, OffsetOfLh>;
        let alice = Arc::new(RwLock::new(Ty::new()));
        let bob = Arc::new(RwLock::new(Ty::new()));
        let t = Arc::new(Foo::default());
        let num_alice = Arc::new(AtomicUsize::new(0));
        let num_bob = Arc::new(AtomicUsize::new(0));
        let now_in = Arc::new(AtomicUsize::new(0));
        let n = 1 << 10;
        let mut vt = Vec::new();
        for i in 0..n {
            let alice = alice.clone();
            let bob = bob.clone();
            let mut f = t.clone();
            let num_alice = num_alice.clone();
            let num_bob = num_bob.clone();
            let now_in = now_in.clone();
            let t = thread::spawn(move || {
                let lh = unsafe {
                    Ty::list_head_of_mut_unchecked(Arc::<Foo>::get_mut_unchecked(&mut f))
                };
                if i & 1 == 0 {
                    let mut aw = alice.write();
                    if Ty::insert_after(&mut *aw, lh) {
                        num_alice.fetch_add(1, Ordering::Relaxed);
                        now_in.store(1, Ordering::Relaxed);
                    }
                } else {
                    let mut bw = bob.write();
                    if Ty::insert_after(&mut *bw, lh) {
                        num_bob.fetch_add(1, Ordering::Relaxed);
                        now_in.store(2, Ordering::Relaxed);
                    }
                }
                let now = now_in.load(Ordering::Acquire);
                match now {
                    1 => {
                        let aw = alice.write();
                        if Ty::detach(lh) {
                            now_in.compare_exchange(1, 0, Ordering::Release, Ordering::Relaxed);
                        }
                    }
                    2 => {
                        let bw = bob.write();
                        if Ty::detach(lh) {
                            now_in.compare_exchange(2, 0, Ordering::Release, Ordering::Relaxed);
                        }
                    }
                    _ => {}
                }
            });
            vt.push(t);
        }
        for t in vt {
            t.join().unwrap();
        }
        let a = num_alice.load(Ordering::Relaxed);
        let b = num_bob.load(Ordering::Relaxed);
        println!("{}", a);
        println!("{}", b);
    }
}
