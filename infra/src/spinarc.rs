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

/// SpinArc is an alternative to Arc<Rwlock> aiming to achieve low
/// memory footprint while keeping memory safety and concurrency
/// safety. Currently it offers only strong_count for reference counting.
extern crate alloc;

use crate::{
    tinyarc::TinyArc as Arc,
    tinyrwlock::{RwLock, RwLockWriteGuard as WriteGuard},
};
use alloc::boxed::Box;
use core::{
    ops::{Deref, DerefMut},
    ptr::NonNull,
};

pub type SpinArc<T> = Arc<RwLock<T>>;
type Uint = u8;

// Can be used to implement intrusive list based on fine grained rwlock.
#[derive(Default, Debug)]
pub struct IlistNode<T: Sized> {
    prev: Option<SpinArc<IlistNode<T>>>,
    next: Option<SpinArc<IlistNode<T>>>,
    // Make it Option<NonNull<T>> so that we can implement sentinel
    // node easier.
    object: Option<NonNull<T>>,
    // To avoid ABA problem.
    version: Uint,
}

impl<T> IlistNode<T> {
    pub fn version(&self) -> usize {
        self.version as usize
    }

    // Version is incremented if this node is inserted to or detached from a list.
    pub fn increment_version(&mut self) -> &mut Self {
        self.version += 1;
        self
    }

    pub const unsafe fn const_new(object: &'static T) -> Self {
        Self {
            version: 0,
            prev: None,
            next: None,
            object: Some(NonNull::from_ref(object)),
        }
    }

    pub const fn default() -> Self {
        Self {
            version: 0,
            prev: None,
            next: None,
            object: None,
        }
    }

    pub fn new(object: T) -> Self {
        let x: Box<_> = Box::new(object);
        Self {
            version: 0,
            prev: None,
            next: None,
            object: Some(Box::leak(x).into()),
        }
    }

    pub fn is_detached(&self) -> bool {
        self.prev.is_none() && self.next.is_none()
    }

    pub fn next(&self) -> Option<&SpinArc<Self>> {
        self.next.as_ref()
    }

    pub fn prev(&self) -> Option<&SpinArc<Self>> {
        self.prev.as_ref()
    }

    // Assume guards are acquired.
    fn do_detach(&mut self, prev: Option<&mut Self>, next: Option<&mut Self>) {
        if let Some(prev) = prev {
            let _ = prev.next.take();
            core::mem::swap(&mut prev.next, &mut self.next);
        };
        if let Some(next) = next {
            let _ = next.prev.take();
            core::mem::swap(&mut next.prev, &mut self.prev);
        }
        self.next = None;
        self.prev = None;
        debug_assert!(self.is_detached());
    }

    pub fn versioned_detach(my_version: Option<usize>, me: &mut SpinArc<Self>) -> bool {
        // FIXME: We are using a stupid algorithm now. When we are unable to
        // get all locks we need, we rollback.
        loop {
            let Some(mut write_me_guard) = me.try_write() else {
                core::hint::spin_loop();
                continue;
            };
            if write_me_guard.is_detached() {
                return false;
            }
            if let Some(version) = my_version {
                if version != write_me_guard.version() {
                    return false;
                }
            };
            let prev = write_me_guard.prev().cloned();
            let mut write_prev_guard = None;
            if prev.is_some() {
                write_prev_guard = unsafe { prev.as_ref().unwrap_unchecked() }.try_write();
                if write_prev_guard.is_none() {
                    core::hint::spin_loop();
                    continue;
                }
            }
            let next = write_me_guard.next().cloned();
            let mut write_next_guard = None;
            if next.is_some() {
                write_next_guard = unsafe { next.as_ref().unwrap_unchecked() }.try_write();
                if write_next_guard.is_none() {
                    core::hint::spin_loop();
                    continue;
                }
            }
            write_me_guard.do_detach(
                write_prev_guard.as_deref_mut(),
                write_next_guard.as_deref_mut(),
            );
            write_me_guard.increment_version();
            return true;
        }
    }

    pub fn detach(me: &mut SpinArc<Self>) -> bool {
        Self::versioned_detach(None, me)
    }

    pub fn versioned_insert_before(
        other_version: Option<usize>,
        other: &mut SpinArc<Self>,
        me: SpinArc<Self>,
    ) -> bool {
        loop {
            let Some(mut write_me_guard) = me.try_write() else {
                core::hint::spin_loop();
                continue;
            };
            if !write_me_guard.is_detached() {
                return false;
            }
            let Some(mut write_other_guard) = other.try_write() else {
                core::hint::spin_loop();
                continue;
            };
            if let Some(version) = other_version {
                if write_other_guard.version() != version {
                    return false;
                }
            };
            let prev = write_other_guard.prev.clone();
            let write_prev_guard = {
                if let Some(prev) = prev.as_ref() {
                    if let Some(guard) = prev.try_write() {
                        Some(guard)
                    } else {
                        core::hint::spin_loop();
                        continue;
                    }
                } else {
                    None
                }
            };
            // Now we have acquired all guards.
            let prev = core::mem::replace(&mut write_other_guard.prev, Some(me.clone()));
            let _ = core::mem::replace(&mut write_me_guard.prev, prev);
            if let Some(mut guard) = write_prev_guard {
                let _ = core::mem::replace(&mut guard.next, Some(me.clone()));
            };
            drop(write_other_guard);
            let _ = core::mem::replace(&mut write_me_guard.next, Some(other.clone()));
            write_me_guard.increment_version();
            return true;
        }
    }

    pub fn insert_before(other: &mut SpinArc<Self>, me: SpinArc<Self>) -> bool {
        Self::versioned_insert_before(None, other, me)
    }

    pub fn versioned_insert_after(
        other_version: Option<usize>,
        other: &mut SpinArc<Self>,
        me: SpinArc<Self>,
    ) -> bool {
        loop {
            let Some(mut write_me_guard) = me.try_write() else {
                core::hint::spin_loop();
                continue;
            };
            if !write_me_guard.is_detached() {
                return false;
            }
            let Some(mut write_other_guard) = other.try_write() else {
                core::hint::spin_loop();
                continue;
            };
            if let Some(version) = other_version {
                if write_other_guard.version() != version {
                    return false;
                }
            };
            let next = write_other_guard.next.clone();
            let write_next_guard = {
                if let Some(next) = next.as_ref() {
                    if let Some(guard) = next.try_write() {
                        Some(guard)
                    } else {
                        core::hint::spin_loop();
                        continue;
                    }
                } else {
                    None
                }
            };
            // Now we have acquired all guards.
            let next = core::mem::replace(&mut write_other_guard.next, Some(me.clone()));
            let _ = core::mem::replace(&mut write_me_guard.next, next);
            if let Some(mut guard) = write_next_guard {
                let _ = core::mem::replace(&mut guard.prev, Some(me.clone()));
            };
            drop(write_other_guard);
            let _ = core::mem::replace(&mut write_me_guard.prev, Some(other.clone()));
            write_me_guard.increment_version();
            return true;
        }
    }

    pub fn insert_after(other: &mut SpinArc<Self>, me: SpinArc<Self>) -> bool {
        Self::versioned_insert_after(None, other, me)
    }

    pub fn remove_after(me: &mut SpinArc<Self>) -> Option<SpinArc<Self>> {
        loop {
            let Some(w) = me.try_write() else {
                core::hint::spin_loop();
                continue;
            };
            w.next()?;
            let Some(wn) = (unsafe { w.next().as_ref().unwrap_unchecked().try_write() }) else {
                core::hint::spin_loop();
                continue;
            };
            let version = wn.version();
            drop(wn);
            let mut next = unsafe { w.next().unwrap_unchecked().clone() };
            drop(w);
            if Node::versioned_detach(Some(version), &mut next) {
                return Some(next);
            }
        }
    }
}

impl<T> Deref for IlistNode<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { self.object.as_ref().unwrap().as_ref() }
    }
}

impl<T> DerefMut for IlistNode<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.object.as_mut().unwrap().as_mut() }
    }
}

impl<T> Drop for IlistNode<T> {
    fn drop(&mut self) {
        // Static data should never reach here.
        if let Some(v) = self.object {
            let x = unsafe { Box::from_raw(v.as_ptr()) };
            drop(x);
        }
    }
}

pub struct MutexIter<'a, T> {
    mutex: WriteGuard<'a, IlistNode<T>>,
    current: Option<SpinArc<IlistNode<T>>>,
}

impl<'a, T> MutexIter<'a, T> {
    pub fn new(head: &'a SpinArc<IlistNode<T>>) -> Self {
        let mutex = head.write();
        let current = mutex.next().cloned();
        Self { mutex, current }
    }
}

impl<T> Iterator for MutexIter<'_, T> {
    type Item = SpinArc<IlistNode<T>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.current.as_ref()?;
        let x = unsafe {
            self.current
                .as_ref()
                .unwrap_unchecked()
                .read()
                .next()
                .cloned()
        };
        core::mem::replace(&mut self.current, x)
    }
}

pub struct VerIter<T> {
    current: SpinArc<IlistNode<T>>,
    version: Uint,
}

impl<T> VerIter<T> {
    pub fn new(head: &SpinArc<IlistNode<T>>) -> Self {
        let r = head.read();
        let version = r.version() as Uint;
        let current = head.clone();
        Self { version, current }
    }
}

impl<T> Iterator for VerIter<T> {
    type Item = (usize, SpinArc<IlistNode<T>>);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let Some(r) = self.current.try_read() else {
                core::hint::spin_loop();
                continue;
            };
            if r.version() != self.version.into() {
                return None;
            }
            let next = r.next().cloned()?;
            let Some(rn) = next.try_read() else {
                core::hint::spin_loop();
                continue;
            };
            let version = rn.version();
            drop(rn);
            drop(r);
            self.current = next;
            self.version = version as Uint;
            return Some((self.version as usize, self.current.clone()));
        }
    }
}

pub(crate) struct Ilist<T: Sized> {
    // FIXME: We can use only one sentinel node if our IlistNode impl
    // is aliasing awared.
    head: SpinArc<IlistNode<T>>,
    tail: SpinArc<IlistNode<T>>,
}

type Node<T> = IlistNode<T>;

impl<T> Ilist<T> {
    pub fn new() -> Self {
        let mut head = Arc::new(RwLock::new(Node::<T>::default()));
        let tail = Arc::new(RwLock::new(Node::<T>::default()));
        Node::<T>::insert_after(&mut head, tail.clone());
        Self { head, tail }
    }

    #[inline]
    fn head(&self) -> &SpinArc<Node<T>> {
        &self.head
    }

    #[inline]
    fn head_mut(&mut self) -> &mut SpinArc<Node<T>> {
        &mut self.head
    }

    #[inline]
    fn tail(&self) -> &SpinArc<Node<T>> {
        &self.tail
    }

    #[inline]
    fn tail_mut(&mut self) -> &mut SpinArc<Node<T>> {
        &mut self.tail
    }

    pub fn is_empty(&self) -> bool {
        self.head()
            .read()
            .next()
            .is_some_and(|v| Arc::is(v, self.tail()))
    }

    pub fn push_back(&mut self, n: SpinArc<Node<T>>) {
        Node::<T>::insert_before(self.tail_mut(), n);
    }

    pub fn pop_front(&mut self) -> Option<SpinArc<Node<T>>> {
        Node::<T>::remove_after(self.head_mut())
    }
}

#[cfg(test)]
mod tests {
    extern crate test;
    use super::*;
    use std::{collections::HashSet, thread};
    use test::{black_box, Bencher};

    #[test]
    fn threaded_insert_after_many() {
        type Node = IlistNode<usize>;
        let head = Arc::new(RwLock::new(Node::new(0)));
        let n = 1024;
        let mut vt = Vec::new();
        for i in 1..n {
            let handle = |id, mut head| {
                let node = Arc::new(RwLock::new(Node::new(id)));
                Node::insert_after(&mut head, node);
            };
            let head = head.clone();
            let t = thread::spawn(move || handle(i, head));
            vt.push(t);
        }
        for t in vt {
            t.join().unwrap();
        }
        let mut cursor = Some(head);
        let mut counter = 0;
        let mut ids = HashSet::new();
        while cursor.is_some() {
            counter += 1;
            let id = **cursor.as_ref().unwrap().read();
            assert!(!ids.contains(&id));
            assert!(ids.insert(id));
            let tmp = cursor.unwrap().read().next.clone();
            cursor = tmp;
        }
        assert_eq!(counter, n);
        for i in 0..n {
            ids.contains(&i);
        }
    }

    #[test]
    fn insert_after_many() {
        type Node = IlistNode<usize>;
        let head = Arc::new(RwLock::new(Node::new(0)));
        let mut prev = head.clone();
        for i in 1..1024 {
            let next = Arc::new(RwLock::new(Node::new(i)));
            Node::insert_after(&mut prev, next);
            let tmp = prev.read().next.as_ref().unwrap().clone();
            prev = tmp;
        }
        let mut cursor = Some(head.clone());
        let mut counter = 0;
        while cursor.is_some() {
            assert_eq!(counter, **cursor.as_ref().unwrap().read());
            counter += 1;
            let tmp = cursor.unwrap().read().next.clone();
            cursor = tmp;
        }

        let mut prev = head.clone();
        for i in 1..2000 {
            let next = Arc::new(RwLock::new(Node::new(0)));
            let wrong_version = Node::versioned_insert_after(Some(i), &mut prev, next);
            assert!(!wrong_version);
        }
    }

    #[test]
    fn insert_before_many() {
        type Node = IlistNode<usize>;
        let mut tail = Arc::new(RwLock::new(Node::new(0)));
        let mut me = tail.clone();
        for i in 1..1024 {
            let prev = Arc::new(RwLock::new(Node::new(i)));
            Node::insert_before(&mut me, prev);
            let tmp = me.read().prev.as_ref().unwrap().clone();
            me = tmp;
        }
        let mut cursor = Some(tail.clone());
        let mut counter = 0;
        while cursor.is_some() {
            assert_eq!(counter, **cursor.as_ref().unwrap().read());
            counter += 1;
            let tmp = cursor.unwrap().read().prev.clone();
            cursor = tmp;
        }

        for i in 0..2000 {
            if i == 1 {
                continue;
            }
            let prev = Arc::new(RwLock::new(Node::new(0)));
            let wrong_version = Node::versioned_insert_before(Some(i), &mut me, prev);
            assert!(!wrong_version);
        }

        let mut a = Arc::new(RwLock::new(Node::new(0)));
        let mut b = Arc::new(RwLock::new(Node::new(1)));
        Node::insert_before(&mut b, a);
        let insert_not_detached = Node::insert_before(&mut me, b);
        assert!(!insert_not_detached);

        let prev = Arc::new(RwLock::new(Node::new(1025)));
        let result = Node::insert_before(&mut tail, prev);
        assert!(result);
        let mut cursor = Some(tail.clone());
        let mut counter = 0;
        while cursor.is_some() {
            if counter == 0 {
                assert_eq!(counter, **cursor.as_ref().unwrap().read());
            } else if counter == 1 {
                assert_eq!(1025, **cursor.as_ref().unwrap().read());
            } else {
                assert_eq!(counter - 1, **cursor.as_ref().unwrap().read());
            }
            counter += 1;
            let tmp = cursor.unwrap().read().prev.clone();
            cursor = tmp;
        }
    }

    #[test]
    fn detach_me() {
        type Node = IlistNode<usize>;
        let mut a = Arc::new(RwLock::new(Node::new(0)));
        let mut b = Arc::new(RwLock::new(Node::new(1)));
        let mut c = Arc::new(RwLock::new(Node::new(2)));
        Node::insert_after(&mut b, c.clone());
        assert!(b.read().prev.is_none());
        assert!(b.read().next.is_some());
        assert!(c.read().prev.is_some());
        assert!(c.read().next.is_none());
        // &b is not detached, so this action should fail.
        assert!(!Node::insert_after(&mut a, b.clone()));
        // &a is detached, so this action should succeed.
        Node::insert_before(&mut b, a.clone());
        assert!(a.read().next.is_some());
        assert!(a.read().prev.is_none());
        assert_eq!(**a.read().next.as_ref().unwrap().read(), 1);
        assert_eq!(**c.read().prev.as_ref().unwrap().read(), 1);

        for i in 1..1000 {
            let wrong_version = Node::versioned_detach(Some(i), &mut b);
            assert!(!wrong_version);
        }

        Node::detach(&mut b);

        let twice_detached = Node::detach(&mut b);
        assert!(!twice_detached);

        assert!(b.read().is_detached());
        assert_eq!(**a.read().next.as_ref().unwrap().read(), 2);
        assert_eq!(**c.read().prev.as_ref().unwrap().read(), 0);
        // We still have a <-> c, if we don't detach any of them, memory leaks.
        Node::detach(&mut a);
    }

    #[test]
    fn remove_after() {
        type Node = IlistNode<usize>;

        let mut me = SpinArc::new(RwLock::new(Node::new(0)));
        let result = Node::remove_after(&mut me);
        assert!(result.is_none());

        let mut a = Arc::new(RwLock::new(Node::new(0)));
        let mut b = Arc::new(RwLock::new(Node::new(1)));
        let mut c = Arc::new(RwLock::new(Node::new(2)));
        Node::insert_after(&mut b, c.clone());
        Node::insert_before(&mut b, a.clone());

        let result = Node::remove_after(&mut a);
        assert_eq!(**result.unwrap().read(), 1);
        assert!(a.read().next.is_some());
        assert!(a.read().prev.is_none());
        assert!(c.read().prev.is_some());
        assert!(c.read().next.is_none());
        assert_eq!(**a.read().next.as_ref().unwrap().read(), 2);
        assert_eq!(**c.read().prev.as_ref().unwrap().read(), 0);
    }

    #[test]
    fn mutex_iter() {
        type Node = IlistNode<usize>;

        let mut node1 = Arc::new(RwLock::new(Node::new(1)));
        let node2 = Arc::new(RwLock::new(Node::new(2)));

        Node::insert_after(&mut node1, node2);

        let mut iter: MutexIter<'_, usize> = MutexIter::new(&node1);

        let mutex_guard: &WriteGuard<'_, IlistNode<usize>> = &iter.mutex;
        assert_eq!(***mutex_guard, 1);

        let current = iter.next().unwrap();
        let current_guard = current.read();
        assert_eq!(**current_guard, 2);

        assert!(iter.next().is_none());
    }

    #[test]
    fn threaded_mutex_iter() {
        use std::time::Duration;
        type Node = IlistNode<usize>;

        let node1 = Arc::new(RwLock::new(Node::new(1)));
        let mut node2 = Arc::new(RwLock::new(Node::new(2)));
        let node3 = Arc::new(RwLock::new(Node::new(3)));

        Node::insert_before(&mut node2, node1.clone());
        Node::insert_after(&mut node2, node3.clone());

        let shared_head = node1.clone();

        let mut readers = Vec::new();
        for i in 0..5 {
            let head = shared_head.clone();
            readers.push(thread::spawn(move || {
                for _ in 0..10 {
                    thread::sleep(Duration::from_millis(5 * i));
                    let iter = MutexIter::new(&head);
                    let vals: Vec<_> = iter.map(|n| **n.read()).collect();
                    assert!(vals == vec![2, 3] || vals == vec![2, 30]);
                }
            }));
        }

        let writer = {
            let head = shared_head.clone();
            thread::spawn(move || {
                for _ in 0..10 {
                    thread::sleep(Duration::from_millis(20));
                    {
                        let mut guard = node3.write();
                        **guard = 30;
                    }
                    thread::sleep(Duration::from_millis(20));
                    {
                        let mut guard = node3.write();
                        **guard = 3;
                    }
                }
            })
        };

        for r in readers {
            r.join().unwrap();
        }
        writer.join().unwrap();
    }

    #[test]
    fn vec_iter() {
        type Node = IlistNode<usize>;

        let mut node1 = Arc::new(RwLock::new(Node::new(1)));
        let node2 = Arc::new(RwLock::new(Node::new(2)));

        Node::insert_after(&mut node1, node2);

        let mut iter: VerIter<usize> = VerIter::new(&node1);

        let current = iter.next().unwrap();
        assert_eq!(current.0, 1);
        assert_eq!(**current.1.read(), 2);

        assert!(iter.next().is_none());

        let mut node1 = Arc::new(RwLock::new(Node::new(1)));
        let node2 = Arc::new(RwLock::new(Node::new(2)));

        Node::insert_after(&mut node1, node2);

        let mut iter: VerIter<usize> = VerIter::new(&node1);

        {
            let mut write_guard = node1.write();
            write_guard.increment_version();
        }

        assert!(iter.next().is_none());
    }

    #[test]
    fn i_list() {
        type Node = IlistNode<usize>;

        let mut i_list: Ilist<usize> = Ilist::new();
        assert!(i_list.is_empty());

        let a = Arc::new(RwLock::new(Node::new(0)));
        let b = Arc::new(RwLock::new(Node::new(1)));
        let c = Arc::new(RwLock::new(Node::new(2)));

        i_list.push_back(a);
        i_list.push_back(b);
        i_list.push_back(c);

        let head = i_list.head();
        assert!(head.read().prev.is_none());
        assert!(head.read().object.is_none());
        assert_eq!(**head.read().next.as_ref().unwrap().read(), 0);

        let tail = i_list.tail();
        assert_eq!(**tail.read().prev.as_ref().unwrap().read(), 2);
        assert!(tail.read().object.is_none());
        assert!(tail.read().next.is_none());

        let first = i_list.pop_front();
        assert_eq!(**first.unwrap().read(), 0);

        let head = i_list.head();
        assert!(head.read().prev.is_none());
        assert!(head.read().object.is_none());
        assert_eq!(**head.read().next.as_ref().unwrap().read(), 1);

        let first = i_list.pop_front();
        assert_eq!(**first.unwrap().read(), 1);

        let head = i_list.head();
        assert!(head.read().prev.is_none());
        assert!(head.read().object.is_none());
        assert_eq!(**head.read().next.as_ref().unwrap().read(), 2);
    }

    #[bench]
    fn bench_insert_after_many(b: &mut Bencher) {
        b.iter(|| {
            let n = 1usize << 16;
            type Node = IlistNode<usize>;
            let head = Arc::new(RwLock::new(Node::new(0)));
            let mut prev = head.clone();
            for i in 1..n {
                let next = Arc::new(RwLock::new(Node::new(i)));
                black_box(Node::insert_after(&mut prev, next));
                let tmp = prev.read().next.as_ref().unwrap().clone();
                prev = tmp;
            }
        });
    }
}
