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

// We are not using Pin APIs here since Pin APIs are unergonomic and
// hard to learn for ordinary developers. We are using a smart pointer
// to wrap a value, it's conventional that the value is pinned. This
// ListHead should be used with smart pointers. It's **NOT**
// concurrent safe.

use crate::{intrusive::Adapter, lifetime::IouMut};
use core::{marker::PhantomData, ptr::NonNull};

#[derive(Default)]
#[repr(transparent)]
pub struct IouListHeadMut<'a, T, A: const Adapter<T>> {
    // We don't want to have to &mut T simultaneously during iterating over the list.
    node: Option<NonNull<ListHead<T, A>>>,
    _lt: PhantomData<&'a mut T>,
}

#[derive(Default, Debug)]
pub struct ListHead<T, A: const Adapter<T>> {
    pub prev: Option<NonNull<ListHead<T, A>>>,
    pub next: Option<NonNull<ListHead<T, A>>>,
    _t: PhantomData<T>,
    _a: PhantomData<A>,
}

pub struct ListHeadIterator<T, A: const Adapter<T>> {
    next: Option<NonNull<ListHead<T, A>>>,
    tail: Option<NonNull<ListHead<T, A>>>,
}

impl<T, A: const Adapter<T>> ListHeadIterator<T, A> {
    pub fn new(head: &ListHead<T, A>, tail: Option<NonNull<ListHead<T, A>>>) -> Self {
        Self {
            next: head.next,
            tail,
        }
    }
}

impl<T, A: const Adapter<T>> Iterator for ListHeadIterator<T, A> {
    type Item = NonNull<ListHead<T, A>>;

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

pub struct ListHeadReverseIterator<T, A: const Adapter<T>> {
    prev: Option<NonNull<ListHead<T, A>>>,
    head: Option<NonNull<ListHead<T, A>>>,
}

impl<T, A: const Adapter<T>> ListHeadReverseIterator<T, A> {
    pub fn new(tail: &ListHead<T, A>, head: Option<NonNull<ListHead<T, A>>>) -> Self {
        Self {
            prev: tail.prev,
            head,
        }
    }
}

impl<T, A: const Adapter<T>> Iterator for ListHeadReverseIterator<T, A> {
    type Item = NonNull<ListHead<T, A>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.prev == self.head {
            return None;
        }
        // FIXME: Shall we unwrap_unchecked directly?
        let Some(current) = self.prev else {
            panic!("Head node is specified, but encountered None during iteration");
        };
        self.prev = unsafe { current.as_ref().prev };
        Some(current)
    }
}

impl<T, A: const Adapter<T>> ListHead<T, A> {
    pub const fn new() -> Self {
        Self {
            prev: None,
            next: None,
            _t: PhantomData,
            _a: PhantomData,
        }
    }

    // Sometimes, we use it in a Binary Search Tree.
    pub fn left(&self) -> Option<NonNull<Self>> {
        self.prev
    }

    pub fn right(&self) -> Option<NonNull<Self>> {
        self.next
    }

    pub fn set_left(&mut self, val: Option<NonNull<Self>>) -> &mut Self {
        self.prev = val;
        self
    }

    pub fn set_right(&mut self, val: Option<NonNull<Self>>) -> &mut Self {
        self.next = val;
        self
    }

    pub fn owner(&self) -> &T {
        let ptr = self as *const _ as *const u8;
        let base = unsafe { ptr.sub(A::offset()) as *const T };
        unsafe { &*base }
    }

    pub unsafe fn owner_mut(&mut self) -> &mut T {
        let ptr = self as *mut _ as *mut u8;
        let base = unsafe { ptr.sub(A::offset()) as *mut T };
        unsafe { &mut *base }
    }

    pub fn is_detached(&self) -> bool {
        self.prev.is_none() && self.next.is_none()
    }

    pub fn insert_after(head: &mut ListHead<T, A>, me: &mut ListHead<T, A>) -> bool {
        unsafe {
            if !me.is_detached() {
                return false;
            }
            let next = core::mem::replace(&mut head.next, Some(NonNull::from_mut(me)));
            let _ = core::mem::replace(&mut me.next, next);
            let prev = next.map_or(Some(NonNull::from_mut(head)), |mut v| {
                core::mem::replace(&mut v.as_mut().prev, Some(NonNull::from_mut(me)))
            });
            debug_assert_eq!(prev, Some(NonNull::from_mut(head)));
            let _ = core::mem::replace(&mut me.prev, prev);
            true
        }
    }

    pub fn safer_insert_after<'b>(
        head: &mut ListHead<T, A>,
        me: &'b mut ListHead<T, A>,
    ) -> Option<IouMut<'b, ListHead<T, A>>> {
        if Self::insert_after(head, me) {
            return Some(IouMut { val: Some(me) });
        }
        None
    }

    pub fn insert_before(tail: &mut ListHead<T, A>, me: &mut ListHead<T, A>) -> bool {
        unsafe {
            if !me.is_detached() {
                return false;
            }
            let prev = core::mem::replace(&mut tail.prev, Some(NonNull::from_mut(me)));
            let _ = core::mem::replace(&mut me.prev, prev);
            let next = prev.map_or(Some(NonNull::from_mut(tail)), |mut v| {
                core::mem::replace(&mut v.as_mut().next, Some(NonNull::from_mut(me)))
            });
            let _ = core::mem::replace(&mut me.next, next);
            true
        }
    }

    pub fn safer_insert_before<'b>(
        tail: &mut ListHead<T, A>,
        me: &'b mut ListHead<T, A>,
    ) -> Option<IouMut<'b, ListHead<T, A>>> {
        if Self::insert_before(tail, me) {
            return Some(IouMut { val: Some(me) });
        }
        None
    }

    pub fn insert_after_with_hook<F: Fn(&ListHead<T, A>)>(
        head: &mut ListHead<T, A>,
        me: &mut ListHead<T, A>,
        hook: F,
    ) -> bool {
        if !Self::insert_after(head, me) {
            return false;
        }
        hook(me);
        true
    }

    pub fn detach(me: &mut ListHead<T, A>) -> bool {
        unsafe {
            if me.is_detached() {
                return false;
            }
            if let Some(mut prev) = me.prev {
                let _ = core::mem::replace(&mut prev.as_mut().next, me.next);
            };
            if let Some(mut next) = me.next {
                let _ = core::mem::replace(&mut next.as_mut().prev, me.prev);
            };
            me.prev = None;
            me.next = None;
            true
        }
    }

    pub fn safer_detach<'b>(
        mut borrow: IouMut<'_, ListHead<T, A>>,
    ) -> Option<IouMut<'b, ListHead<T, A>>> {
        let Some(val) = &mut borrow.val else {
            panic!("Detaching a nil Node");
        };
        if Self::detach(val) {
            return Some(IouMut { val: None });
        }
        None
    }

    pub fn detach_with_hook<F>(me: &mut ListHead<T, A>, hook: F) -> bool
    where
        F: Fn(&ListHead<T, A>),
    {
        if !Self::detach(me) {
            return false;
        }
        hook(me);
        true
    }
}

impl<T, A> !Send for ListHead<T, A> {}
impl<T, A> !Sync for ListHead<T, A> {}

pub struct ListIterator<'a, T, A: const Adapter<T>> {
    it: ListHeadIterator<T, A>,
    _lt: PhantomData<&'a List<T, A>>,
}

impl<'a, T, A: const Adapter<T>> Iterator for ListIterator<'a, T, A> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.it.next()?;
        Some(unsafe { ListHead::owner(node.as_ref()) })
    }
}

pub struct ListIteratorMut<'a, T, A: const Adapter<T>> {
    it: ListHeadIterator<T, A>,
    _lt: PhantomData<&'a List<T, A>>,
}

impl<'a, T, A: const Adapter<T>> Iterator for ListIteratorMut<'a, T, A> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<Self::Item> {
        let mut node = self.it.next()?;
        Some(unsafe { ListHead::owner_mut(node.as_mut()) })
    }
}

// No pop_front or pop_back is provided, since the List relies on context to
// manage lifetime.
#[derive(Debug)]
pub struct List<T, A: const Adapter<T>> {
    head: ListHead<T, A>,
    tail: ListHead<T, A>,
}

impl<T, A: const Adapter<T>> List<T, A> {
    pub const fn new() -> Self {
        Self {
            head: ListHead::new(),
            tail: ListHead::new(),
        }
    }

    pub fn iter(&self) -> ListIterator<'_, T, A> {
        ListIterator {
            it: self.iter_inner(),
            _lt: PhantomData,
        }
    }

    pub fn iter_mut(&mut self) -> ListIteratorMut<'_, T, A> {
        ListIteratorMut {
            it: self.iter_inner_mut(),
            _lt: PhantomData,
        }
    }

    #[inline]
    pub fn init(&mut self) -> bool {
        ListHead::insert_after(&mut self.head, &mut self.tail)
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.head.next == Some(NonNull::from_ref(&self.tail))
    }

    #[inline]
    fn list_head_of_mut(this: &mut T) -> &mut ListHead<T, A> {
        let ptr = this as *mut T as *mut u8;
        let list_head_ptr = unsafe { ptr.add(A::offset()) } as *mut ListHead<T, A>;
        unsafe { &mut *list_head_ptr }
    }

    fn iter_inner_mut(&mut self) -> ListHeadIterator<T, A> {
        ListHeadIterator::new(&self.head, Some(NonNull::from_ref(&self.tail)))
    }

    fn iter_inner(&self) -> ListHeadIterator<T, A> {
        ListHeadIterator::new(&self.head, Some(NonNull::from_ref(&self.tail)))
    }

    fn find_insert_position_by<'a, 'b, Compare>(
        compare: Compare,
        it: ListHeadIterator<T, A>,
        val: &'a T,
    ) -> Option<&'b mut T>
    where
        Compare: Fn(&T, &T) -> core::cmp::Ordering,
        A: 'a,
        A: 'b,
    {
        use core::cmp::Ordering;
        let mut last = None;
        for mut other_val_ptr in it {
            let other_val = unsafe { other_val_ptr.as_mut().owner_mut() };
            let ord = compare(val, other_val);
            if ord == Ordering::Less {
                return last;
            }
            last = Some(other_val);
        }
        last
    }

    #[must_use]
    pub fn push_by<'b, Compare>(
        &mut self,
        compare: Compare,
        val: &'b mut T,
    ) -> Option<IouListHeadMut<'b, T, A>>
    where
        Compare: Fn(&T, &T) -> core::cmp::Ordering,
    {
        let it = self.iter_inner_mut();
        let mut cursor = &mut self.head;
        if let Some(other_val) = Self::find_insert_position_by(compare, it, val) {
            cursor = Self::list_head_of_mut(other_val);
        };
        let node = Self::list_head_of_mut(val);
        let _ = ListHead::safer_insert_after(cursor, node)?;
        Some(IouListHeadMut {
            node: Some(NonNull::from_mut(node)),
            _lt: PhantomData,
        })
    }

    #[must_use]
    pub fn push<'b>(&mut self, val: &'b mut T) -> Option<IouListHeadMut<'b, T, A>> {
        let node = Self::list_head_of_mut(val);
        if !ListHead::insert_before(&mut self.tail, node) {
            return None;
        }
        Some(IouListHeadMut {
            node: Some(NonNull::from_mut(node)),
            _lt: PhantomData,
        })
    }

    #[must_use]
    pub fn pop<'b>(
        &mut self,
        mut borrow: IouListHeadMut<'_, T, A>,
    ) -> Option<IouListHeadMut<'b, T, A>> {
        let Some(node) = &mut borrow.node else {
            panic!("Detaching a nil node");
        };
        if !ListHead::detach(unsafe { node.as_mut() }) {
            return None;
        }
        Some(IouListHeadMut {
            node: None,
            _lt: PhantomData,
        })
    }

    pub fn front(&self) -> Option<&T> {
        if self.is_empty() {
            return None;
        }
        let Some(next) = &self.head.next else {
            panic!("The first node of a non-empty list should be always valid");
        };
        Some(unsafe { next.as_ref().owner() })
    }

    pub fn reorder_chosen_value_by<Compare, Predicate>(
        &mut self,
        compare: Compare,
        choose: Predicate,
    ) -> bool
    where
        Compare: Fn(&T, &T) -> core::cmp::Ordering,
        Predicate: Fn(&T) -> bool,
    {
        let mut chosen = None;
        for v in self.iter_mut() {
            if !choose(v) {
                continue;
            }
            chosen = Some(v);
            break;
        }
        let Some(v) = chosen else {
            return false;
        };
        // To avoid lengthen the borrow region of the `v`, use NonNull<ListHead> here.
        let mut node = NonNull::from_mut(Self::list_head_of_mut(v));
        if !ListHead::detach(unsafe { node.as_mut() }) {
            return false;
        }
        // To avoid lengthen the borrow region of the `v`, create a new `&mut T` from the
        // ListHead.
        let v = unsafe { node.as_mut().owner_mut() };
        let it = self.iter_inner_mut();
        if let Some(cursor) = Self::find_insert_position_by(compare, it, v) {
            return ListHead::insert_after(Self::list_head_of_mut(cursor), unsafe {
                node.as_mut()
            });
        };
        ListHead::insert_after(&mut self.head, unsafe { node.as_mut() })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::impl_simple_intrusive_adapter;
    use core::mem::offset_of;

    impl_simple_intrusive_adapter!(OffsetOfLh, Foo, lh);

    #[derive(Default, Debug)]
    pub struct Foo {
        head: [u8; 8],
        lh: ListHead<Foo, OffsetOfLh>,
        tail: [u8; 8],
    }

    #[test]
    fn test_basic() {
        let f = Foo::default();
        let t = &f.lh;
        let g = t.owner();
        assert_eq!(&f as *const _, g as *const _);
    }

    #[test]
    fn test_insert_and_detach() {
        type Ty = ListHead<Foo, OffsetOfLh>;
        let mut a = Foo::default();
        assert!(a.lh.is_detached());
        let mut b = Foo::default();
        assert!(b.lh.is_detached());
        assert!(Ty::insert_after(&mut a.lh, &mut b.lh));
        assert!(!Ty::insert_after(&mut a.lh, &mut b.lh));
        assert!(!a.lh.is_detached());
        assert!(!b.lh.is_detached());
        Ty::detach(&mut b.lh);
        assert!(a.lh.is_detached());
        assert!(b.lh.is_detached());
        assert!(!Ty::detach(&mut b.lh));
    }

    #[test]
    fn test_insert_before() {
        type Ty = ListHead<Foo, OffsetOfLh>;
        let mut a = Foo::default();
        assert!(a.lh.is_detached());
        let mut b = Foo::default();
        assert!(b.lh.is_detached());
        assert!(Ty::insert_before(&mut a.lh, &mut b.lh));
        assert!(!Ty::insert_before(&mut a.lh, &mut b.lh));
        assert!(!a.lh.is_detached());
        assert!(!b.lh.is_detached());
        Ty::detach(&mut b.lh);
        assert!(a.lh.is_detached());
        assert!(b.lh.is_detached());
    }

    #[test]
    fn test_listiterator() {
        let list_head = ListHead::<Foo, OffsetOfLh>::default();
        let mut iter = ListHeadIterator::new(&list_head, None);

        let result = iter.next();
        assert!(result.is_none());

        let node1 = Box::new(ListHead::<Foo, OffsetOfLh> {
            prev: None,
            next: None,
            _t: PhantomData,
            _a: PhantomData,
        });
        let node2 = Box::new(ListHead::<Foo, OffsetOfLh> {
            prev: None,
            next: None,
            _t: PhantomData,
            _a: PhantomData,
        });

        let node1_leaked = Box::leak(node1);
        let node2_leaked = Box::leak(node2);
        node1_leaked.next = Some(NonNull::from(&mut *node2_leaked));

        let ptr1 = NonNull::from(node1_leaked);
        let ptr2 = NonNull::from(node2_leaked);

        let mut iter = ListHeadIterator::<Foo, OffsetOfLh> {
            next: Some(ptr1),
            tail: Some(ptr2),
        };
        assert_eq!(iter.next(), Some(ptr1));
        assert!(iter.next().is_none());
    }

    #[test]
    #[should_panic(expected = "Tail node is specified, but encountered None during iteration")]
    fn test_listiterator_shoild_panic() {
        let mut dummy = ListHead::<Foo, OffsetOfLh>::default();
        let tail_ptr = NonNull::from(&mut dummy);
        let mut iter = ListHeadIterator::<Foo, OffsetOfLh> {
            next: None,
            tail: Some(tail_ptr),
        };
        iter.next();
    }

    #[test]
    fn test_listreverseiterator() {
        let list_head = ListHead::<Foo, OffsetOfLh>::default();
        let mut iter = ListHeadReverseIterator::new(&list_head, None);

        let result = iter.next();
        assert!(result.is_none());

        let mut node1 = Box::new(ListHead::<Foo, OffsetOfLh> {
            prev: None,
            next: None,
            _t: PhantomData,
            _a: PhantomData,
        });
        let mut node2 = Box::new(ListHead::<Foo, OffsetOfLh> {
            prev: None,
            next: None,
            _t: PhantomData,
            _a: PhantomData,
        });
        let node1_leaked = Box::leak(node1);
        let node2_leaked = Box::leak(node2);
        node1_leaked.prev = Some(NonNull::from(&mut *node2_leaked));

        let ptr1 = NonNull::from(node1_leaked);
        let ptr2 = NonNull::from(node2_leaked);
        let mut iter = ListHeadReverseIterator::<Foo, OffsetOfLh> {
            prev: Some(ptr1),
            head: Some(ptr2),
        };
        assert_eq!(iter.next(), Some(ptr1));
        assert!(iter.next().is_none());
    }

    #[test]
    fn test_adapter() {
        impl_simple_intrusive_adapter!(Node, A, node);

        struct A {
            node: ListHead<A, Node>,
        }

        struct B;

        // Deny following code
        //struct A {
        //    node: ListHead<B, Node>,
        //}
        //struct C {
        //    node: ListHead<B, Node>,
        //}
    }

    #[test]
    fn test_safer_insert_and_detach() {
        impl_simple_intrusive_adapter!(Node, A, node);

        struct A {
            node: ListHead<A, Node>,
            val: usize,
        }

        fn inner(f: &mut ListHead<A, Node>) {
            let mut borrow;
            // Creating a new scope here is critical to assist the borrow checker.
            {
                let mut val = A {
                    node: ListHead::new(),
                    val: 42,
                };
                borrow = ListHead::safer_insert_after(f, &mut val.node).unwrap();
                // The program doesn't compile if the following stmt is omitted.
                borrow = ListHead::safer_detach(borrow).unwrap();
            }
            drop(borrow);
        }

        // The logic hole that current impl by passes borrow check.
        fn hole() {
            let mut borrow;
            // Creating a new scope here is critical to assist the borrow checker.
            {
                let mut val = A {
                    node: ListHead::new(),
                    val: 42,
                };
                let mut f = ListHead::new();
                borrow = ListHead::safer_insert_after(&mut f, &mut val.node).unwrap();
                drop(f);
                // f has been dropped, so that val.node's previous node is dangling,
                // however the program compiles.
                borrow = ListHead::safer_detach(borrow).unwrap();
            }
            drop(borrow);
        }

        let mut head: ListHead<A, Node> = ListHead::new();
        inner(&mut head);
        hole();
    }

    #[test]
    fn test_safer_insert_and_detach_several() {
        impl_simple_intrusive_adapter!(Node, A, node);

        struct A {
            node: ListHead<A, Node>,
            val: usize,
        }

        fn inner(f: &mut ListHead<A, Node>) {
            let mut b0;
            let mut b1;
            // Creating a new scope here is critical to assist the borrow checker.
            {
                let mut val0 = A {
                    node: ListHead::new(),
                    val: 42,
                };
                b0 = ListHead::safer_insert_after(f, &mut val0.node).unwrap();
                let mut val1 = A {
                    node: ListHead::new(),
                    val: 43,
                };
                b1 =
                    ListHead::safer_insert_after(b0.val.as_mut().unwrap(), &mut val1.node).unwrap();
                // The program doesn't compile if we miss either `safer_detach`.
                b0 = ListHead::safer_detach(b0).unwrap();
                b1 = ListHead::safer_detach(b1).unwrap();
            }
            drop(b1);
            drop(b0);
        }

        let mut head: ListHead<A, Node> = ListHead::new();
        inner(&mut head);
    }

    #[test]
    fn test_list_basic() {
        impl_simple_intrusive_adapter!(Node, A, node);

        struct A {
            node: ListHead<A, Node>,
            val: usize,
        }
        let mut l = List::<A, Node>::new();
        l.init();
        let mut borrow;
        {
            let mut val = A {
                node: ListHead::new(),
                val: 42,
            };
            borrow = l.push(&mut val).unwrap();
            for v in l.iter() {
                assert_eq!(v.val, 42);
            }
            borrow = l.pop(borrow).unwrap();
        }
        drop(borrow);
    }

    #[test]
    fn test_list_basic_hole() {
        impl_simple_intrusive_adapter!(Node, A, node);

        struct A {
            node: ListHead<A, Node>,
            val: usize,
        }
        let mut l = List::<A, Node>::new();
        l.init();
        let mut fake = List::new();
        fake.init();
        let mut borrow;
        {
            let mut val = A {
                node: ListHead::new(),
                val: 42,
            };
            borrow = l.push(&mut val).unwrap();
            for v in l.iter() {
                assert_eq!(v.val, 42);
            }
            drop(l);
            // l has been dropped, now val.node's prev and next pointer become dangling,
            // however the program still compiles.
            borrow = fake.pop(borrow).unwrap();
        }
        drop(borrow);
    }

    #[test]
    fn test_list_push_and_pop_several() {
        impl_simple_intrusive_adapter!(Node, A, node);
        struct A {
            node: ListHead<A, Node>,
            val: usize,
        }
        let mut l = List::<A, Node>::new();
        l.init();
        assert!(l.is_empty());
        let mut b0;
        let mut b1;
        {
            let mut val0 = A {
                node: ListHead::new(),
                val: 42,
            };
            let mut val1 = A {
                node: ListHead::new(),
                val: 43,
            };
            b0 = l.push(&mut val0).unwrap();
            b1 = l.push(&mut val1).unwrap();
            let mut index = 0;
            for v in l.iter() {
                match index {
                    0 => {
                        assert_eq!(v.val, 42);
                    }
                    1 => {
                        assert_eq!(v.val, 43);
                    }
                    _ => {}
                }
                index += 1;
            }
            assert_eq!(index, 2);
            b0 = l.pop(b0).unwrap();
            for v in l.iter() {
                assert_eq!(v.val, 43);
            }
            b1 = l.pop(b1).unwrap();
            assert!(l.is_empty());
        }
        drop(b1);
        drop(b0);
    }

    #[test]
    fn test_list_push_by_and_pop_several() {
        impl_simple_intrusive_adapter!(Node, A, node);
        struct A {
            node: ListHead<A, Node>,
            val: usize,
        }
        use core::cmp::Ordering;
        fn compare_val(lhs: &A, rhs: &A) -> Ordering {
            lhs.val.cmp(&rhs.val)
        }
        let mut l = List::<A, Node>::new();
        l.init();
        assert!(l.is_empty());
        let mut b0;
        let mut b1;
        {
            let mut val0 = A {
                node: ListHead::new(),
                val: 42,
            };
            let mut val1 = A {
                node: ListHead::new(),
                val: 43,
            };
            b1 = l.push_by(compare_val, &mut val1).unwrap();
            b0 = l.push_by(compare_val, &mut val0).unwrap();
            let mut index = 0;
            for v in l.iter() {
                match index {
                    0 => {
                        assert_eq!(v.val, 42);
                    }
                    1 => {
                        assert_eq!(v.val, 43);
                    }
                    _ => {}
                }
                index += 1;
            }
            assert_eq!(index, 2);
            b0 = l.pop(b0).unwrap();
            for v in l.iter() {
                assert_eq!(v.val, 43);
            }
            b1 = l.pop(b1).unwrap();
            assert!(l.is_empty());
        }
        drop(b1);
        drop(b0);
    }

    #[test]
    fn test_list_reorder_chosen_value() {
        impl_simple_intrusive_adapter!(Node, A, node);
        struct A {
            node: ListHead<A, Node>,
            val: usize,
        }
        use core::cmp::Ordering;
        fn compare_val(lhs: &A, rhs: &A) -> Ordering {
            lhs.val.cmp(&rhs.val)
        }
        let mut l = List::<A, Node>::new();
        l.init();
        assert!(l.is_empty());
        let mut b0;
        let mut b1;
        {
            let mut val0 = A {
                node: ListHead::new(),
                val: 42,
            };
            let val0_ptr = &val0 as *const A;
            let mut val1 = A {
                node: ListHead::new(),
                val: 43,
            };
            b1 = l.push_by(compare_val, &mut val1).unwrap();
            b0 = l.push_by(compare_val, &mut val0).unwrap();
            if let Some(v) = l.iter_mut().next() {
                v.val = 73;
            };
            assert!(l.reorder_chosen_value_by(compare_val, move |v| v as *const A == val0_ptr));
            let mut index = 0;
            for (index, v) in l.iter().enumerate() {
                match index {
                    0 => {
                        assert_eq!(v.val, 43);
                    }
                    1 => {
                        assert_eq!(v.val, 73);
                    }
                    _ => {}
                }
            }
            b0 = l.pop(b0).unwrap();
            b1 = l.pop(b1).unwrap();
            assert!(l.is_empty());
        }
        drop(b1);
        drop(b0);
    }
}
