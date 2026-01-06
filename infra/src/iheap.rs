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

// An intrusive minimum heap.

use crate::{
    impl_simple_intrusive_adapter,
    intrusive::{Adapter, Nested},
    list::typed_ilist::ListHead,
};
use core::{marker::PhantomData, ptr::NonNull};

#[derive(Default)]
#[repr(transparent)]
pub struct IouMinHeapNodeMut<'a, T, A: const Adapter<T>> {
    // We don't want to have to &mut T simultaneously during iterating over the list.
    node: Option<NonNull<MinHeapNode<T, A>>>,
    _lt: PhantomData<&'a mut T>,
}

#[derive(Default, Debug)]
struct Link<T, A: const Adapter<T>>(PhantomData<(T, A)>);

impl<T, A: const Adapter<T>> const Adapter<MinHeapNode<T, A>> for Link<T, A> {
    fn offset() -> usize {
        core::mem::offset_of!(MinHeapNode<T, A>, link)
    }
}

#[allow(clippy::type_complexity)]
type LinkType<T, A> = ListHead<T, Nested<T, A, MinHeapNode<T, A>, Link<T, A>>>;

#[derive(Default, Debug)]
#[repr(C, align(2))]
pub struct MinHeapNode<T, A: const Adapter<T>> {
    // Put the `link` first so that we don't need to use the complex Nested
    // adapter.
    link: LinkType<T, A>,
    parent: Option<NonNull<MinHeapNode<T, A>>>,
}

impl<T, A: const Adapter<T>> MinHeapNode<T, A> {
    pub const fn new() -> Self {
        Self {
            link: LinkType::new(),
            parent: None,
        }
    }
}

pub struct MinHeap<T, A: const Adapter<T>, Compare>
where
    Compare: Fn(&T, &T) -> core::cmp::Ordering,
{
    borrowed: LinkType<T, A>,
    top: Option<NonNull<MinHeapNode<T, A>>>,
    size: usize,
    compare: Compare,
}

// Compute height and branch directions.
fn compute_path(mut i: usize) -> (usize, usize) {
    let mut height = 0;
    let mut direction = 0;
    while i > 0 {
        direction = (direction << 1) | ((i - 1) & 1);
        i = (i - 1) / 2;
        height += 1;
    }
    (height, direction)
}

impl<T, A: const Adapter<T>, C> MinHeap<T, A, C>
where
    C: Fn(&T, &T) -> core::cmp::Ordering,
{
    pub fn new(compare: C) -> Self {
        Self {
            borrowed: LinkType::new(),
            top: None,
            size: 0,
            compare,
        }
    }

    fn node_of_mut(this: &mut T) -> &mut MinHeapNode<T, A> {
        let ptr = this as *mut T as *mut u8;
        let node_ptr = unsafe { ptr.add(A::offset()) } as *mut MinHeapNode<T, A>;
        unsafe { &mut *node_ptr }
    }

    fn node_of_link_mut(link: &mut LinkType<T, A>) -> &mut MinHeapNode<T, A> {
        let ptr = link as *mut _ as *mut u8;
        let node_ptr = unsafe { ptr.sub(Link::offset()) } as *mut MinHeapNode<T, A>;
        unsafe { &mut *node_ptr }
    }

    fn node_of_link(link: &LinkType<T, A>) -> &MinHeapNode<T, A> {
        let ptr = link as *const _ as *const u8;
        let node_ptr = unsafe { ptr.sub(Link::offset()) } as *const MinHeapNode<T, A>;
        unsafe { &*node_ptr }
    }

    fn owner(node: &MinHeapNode<T, A>) -> &T {
        let ptr = node as *const _ as *const u8;
        let base = unsafe { ptr.sub(A::offset()) as *const T };
        unsafe { &*base }
    }

    fn node_at(
        &self,
        mut i: usize,
        path: &mut (usize, usize),
    ) -> (
        Option<NonNull<MinHeapNode<T, A>>>,
        Option<NonNull<MinHeapNode<T, A>>>,
    ) {
        let (mut height, mut direction) = compute_path(i);
        path.0 = height;
        path.1 = direction;
        let mut current = self.top;
        let mut current_parent = None;
        while height > 0 && current.is_some() {
            current_parent = current;
            if direction & 1 == 0 {
                current = current
                    .as_mut()
                    .and_then(|n| unsafe { n.as_mut() }.link.left())
                    .and_then(|mut n| {
                        Some(NonNull::from_mut(Self::node_of_link_mut(unsafe {
                            n.as_mut()
                        })))
                    });
            } else {
                current = current
                    .as_mut()
                    .and_then(|n| unsafe { n.as_mut() }.link.right())
                    .and_then(|mut n| {
                        Some(NonNull::from_mut(Self::node_of_link_mut(unsafe {
                            n.as_mut()
                        })))
                    });
            }
            direction >>= 1;
            height -= 1;
        }
        (current, current_parent)
    }

    fn bottom_up_adjust(&mut self, val: &T, mut nonnull_node: NonNull<MinHeapNode<T, A>>) {
        loop {
            let Some(mut parent) = unsafe { nonnull_node.as_mut() }.parent else {
                break;
            };
            let parent_val = Self::owner(unsafe { parent.as_mut() });
            if (self.compare)(val, parent_val) != core::cmp::Ordering::Less {
                break;
            }
            self.swap_parent_child(NonNull::from_mut(unsafe { parent.as_mut() }), nonnull_node);
        }
    }

    fn top_down_adjust(&mut self, val: &T, mut node: NonNull<MinHeapNode<T, A>>) {
        loop {
            let mut min_child = None;
            let mut min_val = None;
            if let Some(mut left) = unsafe { node.as_mut() }.link.left() {
                min_child = Some(Self::node_of_link_mut(unsafe { left.as_mut() }));
                min_val = Some(Self::owner(unsafe {
                    min_child.as_ref().unwrap_unchecked()
                }));
            };
            if let Some(mut right) = unsafe { node.as_mut() }.link.right() {
                let right_child = Self::node_of_link_mut(unsafe { right.as_mut() });
                let right_val = Self::owner(right_child);
                if min_val.is_none()
                    || (self.compare)(right_val, unsafe { min_val.unwrap_unchecked() })
                        == core::cmp::Ordering::Less
                {
                    min_child = Some(right_child);
                    min_val = Some(Self::owner(unsafe {
                        min_child.as_ref().unwrap_unchecked()
                    }));
                }
            };
            let Some(tmp) = min_val else {
                break;
            };
            if (self.compare)(val, tmp) == core::cmp::Ordering::Less {
                break;
            }
            self.swap_parent_child(node, NonNull::from_mut(min_child.unwrap()));
        }
    }

    pub fn size(&self) -> usize {
        self.size
    }

    pub fn push<'a>(&mut self, val: &'a mut T) -> Option<IouMinHeapNodeMut<'a, T, A>> {
        let mut path = (0, 0);
        let (current, current_parent) = self.node_at(self.size, &mut path);
        debug_assert!(current.is_none());
        let node = Self::node_of_mut(val);
        node.parent = current_parent;
        let Some(mut parent) = node.parent else {
            self.top = Some(NonNull::from_mut(node));
            self.size += 1;
            return Some(IouMinHeapNodeMut {
                node: Some(node.into()),
                _lt: PhantomData,
            });
        };
        if (1 << path.0) & path.1 == 0 {
            unsafe { parent.as_mut() }
                .link
                .set_left(Some(NonNull::from_mut(&mut node.link)));
        } else {
            unsafe { parent.as_mut() }
                .link
                .set_right(Some(NonNull::from_mut(&mut node.link)));
        }
        // We create a new node here, since we're unable to use split borrows with
        // Self::node_of_mut.
        let nonnull_node = NonNull::from_mut(node);
        self.bottom_up_adjust(val, nonnull_node);
        self.size += 1;
        Some(IouMinHeapNodeMut {
            node: Some(nonnull_node),
            _lt: PhantomData,
        })
    }

    fn swap_parent_child(
        &mut self,
        mut parent: NonNull<MinHeapNode<T, A>>,
        mut child: NonNull<MinHeapNode<T, A>>,
    ) {
        let parent_mut = unsafe { parent.as_mut() };
        let child_mut = unsafe { child.as_mut() };
        core::mem::swap(parent_mut, child_mut);
        parent_mut.parent = Some(child);
        let mut sibling;
        let tmp = Some(NonNull::from_mut(&mut child_mut.link));
        if child_mut.link.left() == tmp {
            child_mut
                .link
                .set_left(Some(NonNull::from_mut(&mut parent_mut.link)));
            sibling = child_mut.link.right();
        } else {
            child_mut
                .link
                .set_right(Some(NonNull::from_mut(&mut parent_mut.link)));
            sibling = child_mut.link.left();
        };
        if let Some(node) = &mut sibling {
            Self::node_of_link_mut(unsafe { node.as_mut() }).parent = Some(child);
        };
        if let Some(mut left) = parent_mut.link.left() {
            Self::node_of_link_mut(unsafe { left.as_mut() }).parent = Some(parent);
        };
        if let Some(mut right) = parent_mut.link.right() {
            Self::node_of_link_mut(unsafe { right.as_mut() }).parent = Some(parent);
        };
        let Some(ancestor) = &mut child_mut.parent else {
            self.top = Some(child);
            return;
        };
        let ancestor = unsafe { ancestor.as_mut() };
        if ancestor.link.left() == Some(NonNull::from_mut(&mut parent_mut.link)) {
            ancestor
                .link
                .set_left(Some(NonNull::from_mut(&mut child_mut.link)));
        } else {
            ancestor
                .link
                .set_right(Some(NonNull::from_mut(&mut child_mut.link)));
        };
    }

    fn is_linked_in_heap(&self, iou: &IouMinHeapNodeMut<T, A>) -> bool {
        if iou.node == self.top {
            return false;
        }
        let Some(node) = &iou.node else {
            panic!("Nil node")
        };
        unsafe { !node.as_ref().parent.is_none() }
    }

    fn is_left_node(parent: &MinHeapNode<T, A>, child: &MinHeapNode<T, A>) -> bool {
        parent.link.left() == Some(NonNull::from_ref(&child.link))
    }

    fn inner_remove(&mut self, mut node: NonNull<MinHeapNode<T, A>>) {
        let mut path = (0, 0);
        let (last, last_parent) = self.node_at(self.size - 1, &mut path);
        let Some(mut last) = last else {
            panic!("Node should not be None when the index is valid")
        };
        let last_mut = unsafe { last.as_mut() };
        let last_link = NonNull::from_mut(&mut last_mut.link);
        let Some(mut last_parent) = last_parent else {
            debug_assert_eq!(node, last);
            self.top = None;
            self.size -= 1;
            return;
        };
        let last_parent_mut = unsafe { last_parent.as_mut() };
        if (1 << path.0) & path.1 == 0 {
            last_parent_mut.link.set_left(None);
        } else {
            last_parent_mut.link.set_right(None);
        }
        self.size -= 1;
        if node == last {
            return;
        }
        let node_mut = unsafe { node.as_mut() };
        // We must be careful core::mem::swap thinks &mut T should not alias each other.
        core::mem::swap(node_mut, last_mut);
        let last_val = Self::owner(last_mut);
        let Some(mut parent) = node_mut.parent else {
            self.top = Some(last);
            self.top_down_adjust(last_val, last);
            return;
        };
        let parent_mut = unsafe { parent.as_mut() };
        let is_left_node = Self::is_left_node(parent_mut, node_mut);
        if is_left_node {
            parent_mut.link.set_left(Some(last_link));
        } else {
            parent_mut.link.set_right(Some(last_link));
        };
        let parent_val = Self::owner(parent_mut);
        if (self.compare)(last_val, parent_val) == core::cmp::Ordering::Less {
            self.bottom_up_adjust(last_val, last);
        } else {
            self.top_down_adjust(last_val, last);
        }
    }

    pub fn remove<'a>(
        &mut self,
        mut iou: IouMinHeapNodeMut<'_, T, A>,
    ) -> Option<IouMinHeapNodeMut<'a, T, A>> {
        if !self.is_linked_in_heap(&iou) {
            let Some(node) = &mut iou.node else {
                panic!("Nil node")
            };
            LinkType::detach(&mut unsafe { node.as_mut() }.link);
            return None;
        }
        let Some(mut node) = iou.node else {
            panic!("Nil node")
        };
        self.inner_remove(node);
        LinkType::insert_after(&mut self.borrowed, &mut unsafe { node.as_mut() }.link);
        Some(IouMinHeapNodeMut {
            node: None,
            _lt: PhantomData,
        })
    }

    pub fn pop(&mut self) -> &mut Self {
        self
    }

    pub fn peek(&self) -> Option<&T> {
        let Some(top) = self.top else {
            return None;
        };
        Some(Self::owner(unsafe { top.as_ref() }))
    }
}

#[cfg(test)]
mod tests {
    extern crate test;
    use super::*;
    use test::Bencher;

    impl_simple_intrusive_adapter!(Node, Foo, node);

    struct Foo {
        node: MinHeapNode<Foo, Node>,
        val: usize,
    }

    #[test]
    fn test_compute_path() {
        assert_eq!(compute_path(0), (0, 0));
        assert_eq!(compute_path(1), (1, 0b0));
        assert_eq!(compute_path(2), (1, 0b1));
        assert_eq!(compute_path(3), (2, 0b00));
        assert_eq!(compute_path(4), (2, 0b10));
        assert_eq!(compute_path(5), (2, 0b01));
        assert_eq!(compute_path(6), (2, 0b11));
        assert_eq!(compute_path(7), (3, 0b000));
        assert_eq!(compute_path(8), (3, 0b100));
        assert_eq!(compute_path(9), (3, 0b010));
        assert_eq!(compute_path(10), (3, 0b110));
        assert_eq!(compute_path(11), (3, 0b001));
        assert_eq!(compute_path(12), (3, 0b101));
        assert_eq!(compute_path(13), (3, 0b011));
        assert_eq!(compute_path(14), (3, 0b111));
    }

    #[test]
    fn test_basic_insertion() {
        let mut heap = MinHeap::<Foo, Node, _>::new(|l, r| l.val.cmp(&r.val));
        let mut path = (0, 0);
        let (n, p) = heap.node_at(0, &mut path);
        assert!(n.is_none());
        assert!(p.is_none());
        assert_eq!(heap.size(), 0);
        let mut n0 = Box::new(Foo {
            node: MinHeapNode::new(),
            val: 42,
        });
        heap.push(&mut n0);
        assert_eq!(heap.size(), 1);
        let top = heap.peek();
        assert!(top.is_some());
        assert_eq!(top.unwrap().val, 42);
        let mut n1 = Box::new(Foo {
            node: MinHeapNode::new(),
            val: 37,
        });
        heap.push(&mut n1);
        assert_eq!(heap.size(), 2);
        let top = heap.peek();
        assert!(top.is_some());
        assert_eq!(top.unwrap().val, 37);
        let mut n2 = Box::new(Foo {
            node: MinHeapNode::new(),
            val: 43,
        });
        heap.push(&mut n2);
        assert_eq!(heap.size(), 3);
        let top = heap.peek();
        assert!(top.is_some());
        assert_eq!(top.unwrap().val, 37);
        let mut n3 = Box::new(Foo {
            node: MinHeapNode::new(),
            val: 23,
        });
        heap.push(&mut n3);
        assert_eq!(heap.size(), 4);
        let top = heap.peek();
        assert!(top.is_some());
        assert_eq!(top.unwrap().val, 23);
    }

    #[bench]
    fn bench_insert(b: &mut Bencher) {
        b.iter(|| {
            let mut heap = MinHeap::<Foo, Node, _>::new(|l, r| l.val.cmp(&r.val));
            let mut n0 = Box::new(Foo {
                node: MinHeapNode::new(),
                val: 0,
            });
            let mut n1 = Box::new(Foo {
                node: MinHeapNode::new(),
                val: 1,
            });
            let mut n2 = Box::new(Foo {
                node: MinHeapNode::new(),
                val: 2,
            });
            let mut n3 = Box::new(Foo {
                node: MinHeapNode::new(),
                val: 3,
            });
            heap.push(&mut n3);
            heap.push(&mut n2);
            heap.push(&mut n1);
            heap.push(&mut n0);
        });
    }

    #[bench]
    fn bench_insert_std(b: &mut Bencher) {
        use std::collections::BinaryHeap;
        #[derive(Eq, Ord, PartialEq, PartialOrd)]
        struct Foo {
            val: usize,
        };
        b.iter(|| {
            let mut heap = BinaryHeap::new();
            let mut n0 = Box::new(Foo { val: 0 });
            let mut n1 = Box::new(Foo { val: 1 });
            let mut n2 = Box::new(Foo { val: 2 });
            let mut n3 = Box::new(Foo { val: 3 });
            heap.push(n3);
            heap.push(n2);
            heap.push(n1);
            heap.push(n0);
        });
    }
}
