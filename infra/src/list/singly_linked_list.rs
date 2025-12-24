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

use alloc::boxed::Box;
use core::{fmt, marker::PhantomData, mem, ops::Drop, ptr::NonNull};

/// An intrusive linked list
#[derive(Copy, Clone)]
pub struct SinglyLinkedList<T> {
    head: Option<NonNull<T>>,
    _marker: PhantomData<T>,
}

unsafe impl<T: Send> Send for SinglyLinkedList<T> {}

impl<T> Default for SinglyLinkedList<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> SinglyLinkedList<T> {
    /// Create a new SinglyLinkedList
    pub const fn new() -> Self {
        SinglyLinkedList {
            head: None,
            _marker: PhantomData,
        }
    }

    /// Return `true` if the list is empty
    pub fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    /// Push `item` to the front of the list
    /// # SAFETY
    /// - `item` must be a valid, non-null pointer
    /// - `item` must point to valid memory that can be written to
    pub unsafe fn push(&mut self, item: NonNull<T>) {
        // Making sure T is big enough to memory next pointer.
        debug_assert!(mem::size_of::<T>() >= mem::size_of::<Option<NonNull<T>>>());
        let item_ptr = item.as_ptr() as *mut Option<NonNull<T>>;
        *item_ptr = self.head;
        self.head = Some(item);
    }

    /// Try to remove the first item in the list
    pub fn pop(&mut self) -> Option<NonNull<T>> {
        match self.is_empty() {
            true => None,
            false => {
                let item = self.head?;
                let next_ptr = item.as_ptr() as *mut Option<NonNull<T>>;
                unsafe {
                    self.head = *next_ptr;
                }
                Some(item)
            }
        }
    }

    /// Return an iterator over the items in the list
    pub fn iter(&self) -> Iter<'_, T> {
        Iter {
            curr: self.head,
            list: PhantomData,
        }
    }

    /// Return an mutable iterator over the items in the list
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut {
            prev: &mut self.head as *mut Option<NonNull<T>>,
            curr: self.head,
            list: PhantomData,
        }
    }
}

impl<T> fmt::Debug for SinglyLinkedList<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// An iterator over the linked list
pub struct Iter<'a, T> {
    curr: Option<NonNull<T>>,
    list: PhantomData<&'a SinglyLinkedList<T>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = NonNull<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.curr.is_none() {
            None
        } else {
            let item = self.curr;
            // SAFETY: We have checked that self.curr is not null
            let next = item?.as_ptr() as *const Option<NonNull<T>>;
            unsafe {
                self.curr = *next;
            }
            item
        }
    }
}

/// Represent a mutable node in `SinglyLinkedList`
pub struct ListNode<'a, T> {
    prev: *mut Option<NonNull<T>>,
    curr: NonNull<T>,
    _marker: PhantomData<&'a mut T>,
}

impl<T> ListNode<'_, T> {
    /// Remove the node from the list
    pub fn pop(self) -> NonNull<T> {
        unsafe {
            // skip the curr one.
            let curr_ptr = self.curr.as_ptr() as *mut Option<NonNull<T>>;
            *(self.prev) = *curr_ptr;
        }
        self.curr
    }

    /// Returns the pointed address
    pub fn value(&self) -> NonNull<T> {
        self.curr
    }
}

/// A mutable iterator over the linked list
pub struct IterMut<'a, T> {
    list: PhantomData<&'a mut SinglyLinkedList<T>>,
    prev: *mut Option<NonNull<T>>,
    curr: Option<NonNull<T>>,
}

impl<'a, T: 'a> Iterator for IterMut<'a, T> {
    type Item = ListNode<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.curr.is_none() {
            None
        } else {
            let cur_node = self.curr?;
            let res = ListNode {
                prev: self.prev,
                curr: cur_node,
                _marker: PhantomData,
            };
            self.prev = cur_node.as_ptr() as *mut Option<NonNull<T>>;
            // SAFETY: We have checked that self.curr is not null
            self.curr = unsafe { *self.prev };
            Some(res)
        }
    }
}

pub struct Node<T> {
    next: Link<T>,
    val: T,
}

pub struct List<T> {
    head: Link<T>,
    size: usize,
}

impl<T> Default for List<T> {
    fn default() -> Self {
        List::<T> {
            head: None,
            size: 0,
        }
    }
}

impl<T> Drop for List<T> {
    fn drop(&mut self) {
        while !self.is_empty() {
            self.pop();
        }
    }
}

impl<T> List<T> {
    pub const fn new() -> Self {
        List::<T> {
            head: None,
            size: 0,
        }
    }

    pub fn size(&self) -> usize {
        self.size
    }

    pub fn is_empty(&self) -> bool {
        debug_assert_eq!(self.head.is_none(), self.size == 0);
        self.size == 0
    }

    pub fn push(&mut self, val: T) -> &mut Self {
        let mut new_node = Box::new(Node::<T>::new(val));
        let old_head = self.head.take();
        new_node.next = old_head;
        self.head = Some(new_node);
        self.size += 1;
        self
    }

    pub fn pop(&mut self) -> Option<T> {
        match self.head.take() {
            None => None,
            Some(mut old_head) => {
                debug_assert!(self.size > 0);
                mem::swap(&mut self.head, &mut old_head.next);
                self.size -= 1;
                Some(old_head.take())
            }
        }
    }
}

type Link<T> = Option<Box<Node<T>>>;

// A safe singly linked list. External code should **NOT** rely on the address of a node in the list.
impl<T> Node<T> {
    const fn new(val: T) -> Self {
        Self { next: None, val }
    }

    fn as_ref(&self) -> &T {
        &self.val
    }

    fn as_mut(&mut self) -> &mut T {
        &mut self.val
    }

    fn take(self) -> T {
        self.val
    }

    // O(1) insertion.
    fn insert(&mut self, val: T) -> &mut Self {
        let mut new_node = Box::<Node<T>>::new(Node::<T> { next: None, val });
        mem::swap(&mut new_node.val, &mut self.val);
        mem::swap(&mut new_node.next, &mut self.next);
        let old_next = mem::replace(&mut self.next, Some(new_node));
        debug_assert!(old_next.is_none());
        self
    }

    // O(1) removal.
    fn remove(&mut self) -> Option<Self> {
        match self.next.take() {
            None => None,
            Some(mut old_next) => {
                mem::swap(&mut old_next.next, &mut self.next);
                debug_assert!(old_next.next.is_none());
                mem::swap(&mut old_next.val, &mut self.val);
                Some(*old_next)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    extern crate test;

    use super::*;
    use crate::list::singly_linked_list;
    use test::{black_box, Bencher};

    #[derive(Debug)]
    struct BenchNode {
        _next: usize,
        _payload: [u8; 64],
    }
    impl BenchNode {
        fn new() -> Self {
            Self {
                _next: 0,
                _payload: [0; 64],
            }
        }
    }

    #[bench]
    #[allow(clippy::unit_arg)]
    fn raw_list_bench_push(b: &mut Bencher) {
        let n = 1 << 16;
        let mut l = SinglyLinkedList::new();
        b.iter(|| unsafe {
            for _ in 0..n {
                let v = Box::new(BenchNode::new());
                let ptr = unsafe { NonNull::new_unchecked(Box::into_raw(v)) };
                unsafe { l.push(ptr) };
            }

            while let Some(ptr) = l.pop() {
                unsafe {
                    let _ = Box::from_raw(ptr.as_ptr());
                }
            }
        });
    }

    #[bench]
    #[allow(clippy::unit_arg)]
    fn raw_list_bench_push_and_pop(b: &mut Bencher) {
        let n = 1 << 16;
        b.iter(|| unsafe {
            let mut l = SinglyLinkedList::new();

            // Push
            for _ in 0..n {
                let v = Box::new(BenchNode::new());
                let ptr = unsafe { NonNull::new_unchecked(Box::into_raw(v)) };
                unsafe { l.push(ptr) };
            }
            // Pop and Free
            while let Some(ptr) = l.pop() {
                unsafe {
                    let _ = Box::from_raw(ptr.as_ptr());
                }
            }
        });
    }

    #[test]
    fn singlylinkedlist_basic_ops() {
        let mut list = SinglyLinkedList::<usize>::new();

        // Simulating heap allocating usize
        let v1 = Box::new(100usize);
        let v2 = Box::new(200usize);
        let p1 = unsafe { NonNull::new_unchecked(Box::into_raw(v1)) };
        let p2 = unsafe { NonNull::new_unchecked(Box::into_raw(v2)) };
        unsafe {
            list.push(p1);
            list.push(p2);
        }
        let popped1 = list.pop().unwrap();
        assert_eq!(popped1, p2);

        let popped2 = list.pop().unwrap();
        assert_eq!(popped2, p1);
        assert!(list.pop().is_none());
        // clear memory
        unsafe {
            let _ = Box::from_raw(p1.as_ptr());
            let _ = Box::from_raw(p2.as_ptr());
        }
    }
    #[test]
    fn listnode_pop_via_iter_mut() {
        #[repr(C)]
        struct Node {
            next: usize,
            data: usize,
        }

        let mut list = SinglyLinkedList::<Node>::new();

        let v1 = Box::new(Node { next: 0, data: 1 });
        let v2 = Box::new(Node { next: 0, data: 2 });
        let v3 = Box::new(Node { next: 0, data: 3 });
        unsafe {
            list.push(NonNull::new_unchecked(Box::into_raw(v1)));
            list.push(NonNull::new_unchecked(Box::into_raw(v2))); // 2 在中间
            list.push(NonNull::new_unchecked(Box::into_raw(v3))); // 3 在头
        }

        {
            let mut iter = list.iter_mut();
            let node3 = iter.next().unwrap();
            assert_eq!(unsafe { node3.value().as_ref().data }, 3);

            let node2 = iter.next().unwrap();
            assert_eq!(unsafe { node2.value().as_ref().data }, 2);

            let popped_ptr = node2.pop();
            unsafe {
                let _ = Box::from_raw(popped_ptr.as_ptr());
            }
        }

        let p3 = list.pop().unwrap();
        assert_eq!(unsafe { p3.as_ref().data }, 3);

        let p1 = list.pop().unwrap();
        assert_eq!(unsafe { p1.as_ref().data }, 1);
        unsafe {
            let _ = Box::from_raw(p3.as_ptr());
            let _ = Box::from_raw(p1.as_ptr());
        }
    }

    #[test]
    fn create_new_list() {
        let head = Node::<i32> {
            val: -1,
            next: None,
        };
        assert_eq!(head.val, -1);
    }

    #[test]
    fn insert_node() {
        let mut head = Node::<i32> {
            val: -1,
            next: None,
        };
        let new_node = head.insert(1024);
        assert_eq!(new_node.val, 1024);
        assert_eq!(new_node.next.as_ref().unwrap().val, -1);
    }

    #[test]
    fn remove_node() {
        let mut n0 = Node::<i32>::new(-1);
        let n1 = n0.insert(1024);
        assert_eq!(n1.val, 1024);
        let n2 = n1.remove();
        assert_eq!(n1.val, -1);
        assert!(n2.is_some());
        assert_eq!(n2.unwrap().val, 1024);
    }

    #[test]
    fn make_sequence_and_count() {
        let mut head = Node::<i32>::new(0);
        for i in 1..1024 {
            head.insert(i);
        }
        let mut count = 1;
        let mut current = &mut head;
        while current.next.is_some() {
            current = current.next.as_mut().unwrap();
            count += 1;
            assert_eq!(current.val, 1024 - count);
        }
        assert_eq!(count, 1024);
    }

    #[test]
    fn make_sequence_and_remove() {
        let mut head = Node::<i32>::new(0);
        for i in 1..1024 {
            head.insert(i);
        }
        let mut count = 0;
        while head.next.is_some() {
            head.remove();
            count += 1;
        }
        assert_eq!(count, 1023);
        assert!(head.remove().is_none());
    }

    #[bench]
    fn bench_make_sequence_and_remove(b: &mut Bencher) {
        b.iter(|| {
            let n = 1 << 16;
            let mut head = Node::<i32>::new(0);
            for i in 1..n {
                black_box(head.insert(i));
            }
            while head.next.is_some() {
                black_box(head.remove());
            }
        });
    }

    #[test]
    fn test_push() {
        let n = 1usize << 16;
        let mut l = List::<usize>::default();
        for i in 0..n {
            l.push(i);
        }
        assert_eq!(l.size(), n);
    }

    // This test indicates the List should implement Drop trait itself to destory.
    // Or the destruction procedure will hit stackoverflow, since the boxes are
    // destroyed recursively.
    #[bench]
    fn bench_push(b: &mut Bencher) {
        b.iter(|| {
            let n = 1usize << 16;
            let mut l = List::<usize>::default();
            let mut count = 0;
            count += 1;
            for i in 0..n {
                black_box(l.push(i));
            }
            assert_eq!(count * n, l.size());
        });
    }

    #[bench]
    fn bench_push_and_pop(b: &mut Bencher) {
        b.iter(|| {
            let n = 1usize << 16;
            let mut l = List::<usize>::default();
            for i in 0..n {
                black_box(l.push(i));
            }
            assert_eq!(l.size(), n);
            while !l.is_empty() {
                black_box(l.pop());
            }
            assert!(l.is_empty());
        });
    }

    #[test]
    fn singlylinkedlist_pop_from_empty() {
        let mut l: singly_linked_list::SinglyLinkedList<usize> = SinglyLinkedList::default();
        let result = l.pop();
        assert!(result.is_none());
    }

    #[test]
    fn singlylinkedlist_iter() {
        let mut list: singly_linked_list::SinglyLinkedList<usize> = SinglyLinkedList::new();
        let data1: usize = 1;
        let data2: usize = 2;

        let v1 = Box::new(data1);
        let v2 = Box::new(data2);
        let ptr1 = unsafe { NonNull::new_unchecked(Box::into_raw(v1)) };
        let ptr2 = unsafe { NonNull::new_unchecked(Box::into_raw(v2)) };
        unsafe {
            list.push(ptr2);
            list.push(ptr1);
        }
        let mut iter = list.iter();
        assert_eq!(iter.next(), Some(ptr1));
        assert_eq!(iter.next(), Some(ptr2));
        assert!(iter.next().is_none());

        unsafe {
            let _ = Box::from_raw(ptr1.as_ptr());
            let _ = Box::from_raw(ptr2.as_ptr());
        }
    }

    #[test]
    fn listnode_push_pop() {
        let mut node1 = Box::new(100usize);
        let mut node2 = Box::new(200usize);

        let ptr1 = unsafe { NonNull::new_unchecked(Box::into_raw(node1)) };
        let ptr2 = unsafe { NonNull::new_unchecked(Box::into_raw(node2)) };

        unsafe {
            let node1_next_ptr = ptr1.as_ptr() as *mut Option<NonNull<usize>>;
            *node1_next_ptr = Some(ptr2);
        }

        let prev_ptr = unsafe { ptr1.as_ptr() as *mut Option<NonNull<usize>> };

        let list_node = ListNode {
            prev: prev_ptr,
            curr: ptr2,
            _marker: PhantomData,
        };

        assert_eq!(list_node.value(), ptr2);

        list_node.pop();

        unsafe {
            let node1_next = *prev_ptr;
            let node2_payload_as_next = ptr2.as_ptr() as *mut Option<NonNull<usize>>;
            let expected_next = *node2_payload_as_next;

            assert_eq!(node1_next, expected_next);

            // Clean up
            let _ = Box::from_raw(ptr1.as_ptr());
            let _ = Box::from_raw(ptr2.as_ptr());
        }
    }
}
