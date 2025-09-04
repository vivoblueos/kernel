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
use core::{fmt, marker::PhantomData, mem, ops::Drop, ptr};

/// An intrusive linked list
#[derive(Copy, Clone)]
pub struct SinglyLinkedList {
    head: *mut usize,
}

/// SAFETY: SinglyLinkedList only contains a raw pointer field, which is safe to share between threads
/// because all modification operations require exclusive mutable reference (&mut self),
/// ensuring that only one thread can modify the list at any time.
unsafe impl Send for SinglyLinkedList {}

impl Default for SinglyLinkedList {
    fn default() -> Self {
        Self::new()
    }
}

impl SinglyLinkedList {
    /// Create a new SinglyLinkedList
    pub const fn new() -> SinglyLinkedList {
        SinglyLinkedList {
            head: ptr::null_mut(),
        }
    }

    /// Return `true` if the list is empty
    pub fn is_empty(&self) -> bool {
        self.head.is_null()
    }

    /// Push `item` to the front of the list
    /// # SAFETY
    /// - `item` must be a valid, non-null pointer
    /// - `item` must point to valid memory that can be written to
    pub unsafe fn push(&mut self, item: *mut usize) {
        debug_assert!(!item.is_null(), "item cannot be null");

        *item = self.head as usize;
        self.head = item;
    }

    /// Try to remove the first item in the list
    pub fn pop(&mut self) -> Option<*mut usize> {
        match self.is_empty() {
            true => None,
            false => {
                let item = self.head;
                // SAFETY: We have checked that self.head is not null, and item points to
                // a valid address stored by previous push operations
                self.head = unsafe { *item as *mut usize };
                Some(item)
            }
        }
    }

    /// Return an iterator over the items in the list
    pub fn iter(&self) -> Iter {
        Iter {
            curr: self.head,
            list: PhantomData,
        }
    }

    /// Return an mutable iterator over the items in the list
    pub fn iter_mut(&mut self) -> IterMut {
        IterMut {
            prev: &mut self.head as *mut *mut usize as *mut usize,
            curr: self.head,
            list: PhantomData,
        }
    }
}

impl fmt::Debug for SinglyLinkedList {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// An iterator over the linked list
pub struct Iter<'a> {
    curr: *mut usize,
    list: PhantomData<&'a SinglyLinkedList>,
}

impl Iterator for Iter<'_> {
    type Item = *mut usize;

    fn next(&mut self) -> Option<Self::Item> {
        if self.curr.is_null() {
            None
        } else {
            let item = self.curr;
            // SAFETY: We have checked that self.curr is not null
            let next = unsafe { *item as *mut usize };
            self.curr = next;
            Some(item)
        }
    }
}

/// Represent a mutable node in `SinglyLinkedList`
pub struct ListNode {
    prev: *mut usize,
    curr: *mut usize,
}

impl ListNode {
    /// Remove the node from the list
    pub fn pop(self) -> *mut usize {
        debug_assert!(!self.prev.is_null(), "prev pointer cannot be null");
        debug_assert!(!self.curr.is_null(), "curr pointer cannot be null");

        // SAFETY: We have checked that self.prev and self.curr are not null
        // If prev or curr is null, the list is corrupted
        unsafe {
            // skip the curr one.
            *(self.prev) = *(self.curr);
        }
        self.curr
    }

    /// Returns the pointed address
    pub fn value(&self) -> *mut usize {
        self.curr
    }
}

/// A mutable iterator over the linked list
pub struct IterMut<'a> {
    list: PhantomData<&'a mut SinglyLinkedList>,
    prev: *mut usize,
    curr: *mut usize,
}

impl Iterator for IterMut<'_> {
    type Item = ListNode;

    fn next(&mut self) -> Option<Self::Item> {
        if self.curr.is_null() {
            None
        } else {
            let res = ListNode {
                prev: self.prev,
                curr: self.curr,
            };
            self.prev = self.curr;
            // SAFETY: We have checked that self.curr is not null
            self.curr = unsafe { *self.curr as *mut usize };
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
        assert_eq!(self.head.is_none(), self.size == 0);
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
                assert!(self.size > 0);
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
        assert!(old_next.is_none());
        self
    }

    // O(1) removal.
    fn remove(&mut self) -> Option<Self> {
        match self.next.take() {
            None => None,
            Some(mut old_next) => {
                mem::swap(&mut old_next.next, &mut self.next);
                assert!(old_next.next.is_none());
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
    use test::{black_box, Bencher};

    #[bench]
    #[allow(clippy::unit_arg)]
    fn raw_list_bench_push(b: &mut Bencher) {
        let n = 1 << 16;
        let mut l = SinglyLinkedList::new();
        b.iter(|| unsafe {
            for _ in 0..n {
                let v = Box::new(0usize);
                // Let the memory leak.
                black_box(l.push(Box::<usize>::into_raw(v)))
            }
        });
    }

    #[bench]
    #[allow(clippy::unit_arg)]
    fn raw_list_bench_push_and_pop(b: &mut Bencher) {
        let n = 1 << 16;
        let mut l = SinglyLinkedList::new();
        b.iter(|| unsafe {
            for _ in 0..n {
                let v = Box::new(0usize);
                // Let the memory leak.
                black_box(l.push(Box::<usize>::into_raw(v)))
            }
            while !l.is_empty() {
                l.pop();
            }
        });
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
        let mut l = SinglyLinkedList::default();
        let result = l.pop();
        assert!(result.is_none());
    }

    #[test]
    fn singlylinkedlist_iter() {
        let mut list = SinglyLinkedList::new();
        let data1: usize = 1;
        let data2: usize = 2;
        let ptr1 = &data1 as *const usize as *mut usize;
        let ptr2 = &data2 as *const usize as *mut usize;
        unsafe {
            list.push(ptr2);
            list.push(ptr1);
        }
        let mut iter = list.iter();
        assert_eq!(iter.next(), Some(ptr1));
        assert_eq!(iter.next(), Some(ptr2));
        assert!(iter.next().is_none());
    }

    #[test]
    fn listnode_push_pop() {
        let mut prev_next = 0x2000usize;
        let mut curr_next = 0x3000usize;
        let list_node = ListNode {
            prev: &mut prev_next as *mut usize,
            curr: &mut curr_next as *mut usize,
        };
        assert!(!list_node.value().is_null());
        list_node.pop();
        assert_eq!(prev_next, 0x3000usize);
    }
}
