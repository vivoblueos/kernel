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
    list::typed_ilist::{ListHead, ListHeadIterator},
};
use core::{marker::PhantomData, ptr::NonNull};

#[derive(Default)]
#[repr(transparent)]
pub struct IouMinHeapNodeMut<'a, T, A: const Adapter<T>> {
    node: Option<NonNull<MinHeapNode<T, A>>>,
    _lt: PhantomData<&'a mut T>,
}

impl<T, A: const Adapter<T>> IouMinHeapNodeMut<'_, T, A> {
    pub const fn new() -> Self {
        Self {
            node: None,
            _lt: PhantomData,
        }
    }

    pub unsafe fn from_mut(node: &mut T) -> Self {
        Self {
            node: Some(NonNull::from_mut(MinHeapNode::<T, A>::node_of_mut(node))),
            _lt: PhantomData,
        }
    }
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

#[allow(clippy::type_complexity)]
type LinkTypeIterator<T, A> = ListHeadIterator<T, Nested<T, A, MinHeapNode<T, A>, Link<T, A>>>;

#[derive(Default, Debug)]
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

    fn node_of_mut(this: &mut T) -> &mut Self {
        let ptr = this as *mut T as *mut u8;
        let node_ptr = unsafe { ptr.add(A::offset()) } as *mut Self;
        unsafe { &mut *node_ptr }
    }

    fn node_of_link_mut(link: &mut LinkType<T, A>) -> &mut Self {
        let ptr = link as *mut _ as *mut u8;
        let node_ptr = unsafe { ptr.sub(Link::offset()) } as *mut Self;
        unsafe { &mut *node_ptr }
    }

    fn node_of_link(link: &LinkType<T, A>) -> &Self {
        let ptr = link as *const _ as *const u8;
        let node_ptr = unsafe { ptr.sub(Link::offset()) } as *const Self;
        unsafe { &*node_ptr }
    }

    fn owner(node: &Self) -> &T {
        let ptr = node as *const _ as *const u8;
        let base = unsafe { ptr.sub(A::offset()) as *const T };
        unsafe { &*base }
    }
}

#[derive(Debug)]
pub struct MinHeap<T, A: const Adapter<T>, Compare>
where
    Compare: Fn(&T, &T) -> core::cmp::Ordering,
{
    popped: LinkType<T, A>,
    root: Option<NonNull<MinHeapNode<T, A>>>,
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
    pub const fn new(compare: C) -> Self {
        Self {
            popped: LinkType::new(),
            root: None,
            size: 0,
            compare,
        }
    }

    pub fn iou_owner<'a>(iou: &IouMinHeapNodeMut<'a, T, A>) -> Option<&'a T>
    where
        A: 'a,
    {
        let node = iou.node?;
        Some(MinHeapNode::<T, A>::owner(unsafe { node.as_ref() }))
    }

    #[allow(clippy::type_complexity)]
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
        let mut current = self.root;
        let mut current_parent = None;
        while height > 0 && current.is_some() {
            current_parent = current;
            if direction & 1 == 0 {
                current = current
                    .as_mut()
                    .and_then(|n| unsafe { n.as_mut() }.link.left())
                    .map(|mut n| {
                        NonNull::from_mut(MinHeapNode::node_of_link_mut(unsafe { n.as_mut() }))
                    });
            } else {
                current = current
                    .as_mut()
                    .and_then(|n| unsafe { n.as_mut() }.link.right())
                    .map(|mut n| {
                        NonNull::from_mut(MinHeapNode::node_of_link_mut(unsafe { n.as_mut() }))
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
            let parent_val = MinHeapNode::owner(unsafe { parent.as_mut() });
            if (self.compare)(val, parent_val) != core::cmp::Ordering::Less {
                break;
            }
            unsafe { self.swap_nodes(NonNull::from_mut(unsafe { parent.as_mut() }), nonnull_node) };
        }
    }

    fn top_down_adjust(&mut self, val: &T, mut node: NonNull<MinHeapNode<T, A>>) {
        loop {
            let mut min_child = None;
            let mut min_val = None;
            if let Some(mut left) = unsafe { node.as_mut() }.link.left() {
                min_child = Some(MinHeapNode::node_of_link_mut(unsafe { left.as_mut() }));
                min_val = Some(MinHeapNode::owner(unsafe {
                    min_child.as_ref().unwrap_unchecked()
                }));
            };
            if let Some(mut right) = unsafe { node.as_mut() }.link.right() {
                let right_child = MinHeapNode::node_of_link_mut(unsafe { right.as_mut() });
                let right_val = MinHeapNode::owner(right_child);
                if min_val.is_none()
                    || (self.compare)(right_val, unsafe { min_val.unwrap_unchecked() })
                        == core::cmp::Ordering::Less
                {
                    min_child = Some(right_child);
                    min_val = Some(MinHeapNode::owner(unsafe {
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
            unsafe { self.swap_nodes(node, NonNull::from_mut(min_child.unwrap())) };
        }
    }

    pub fn size(&self) -> usize {
        self.size
    }

    pub fn push<'a>(&mut self, val: &'a mut T) -> Option<IouMinHeapNodeMut<'a, T, A>> {
        let node = MinHeapNode::node_of_mut(val);
        if node.parent.is_some() || !node.link.is_detached() {
            return None;
        }
        let mut path = (0, 0);
        let (current, current_parent) = self.node_at(self.size, &mut path);
        debug_assert!(current.is_none());
        node.parent = current_parent;
        self.size += 1;
        let Some(mut parent) = node.parent else {
            debug_assert_eq!(path.0, 0);
            self.root = Some(NonNull::from_mut(node));
            return Some(IouMinHeapNodeMut {
                node: Some(node.into()),
                _lt: PhantomData,
            });
        };
        if (1 << (path.0 - 1)) & path.1 == 0 {
            debug_assert_eq!(unsafe { parent.as_ref() }.link.left(), None);
            unsafe { parent.as_mut() }
                .link
                .set_left(Some(NonNull::from_mut(&mut node.link)));
        } else {
            debug_assert_eq!(unsafe { parent.as_ref() }.link.right(), None);
            unsafe { parent.as_mut() }
                .link
                .set_right(Some(NonNull::from_mut(&mut node.link)));
        }
        // We create a new node here, since we're unable to use split borrows with
        // Self::node_of_mut.
        let nonnull_node = NonNull::from_mut(node);
        self.bottom_up_adjust(val, nonnull_node);
        Some(IouMinHeapNodeMut {
            node: Some(nonnull_node),
            _lt: PhantomData,
        })
    }

    unsafe fn swap_nodes(
        &mut self,
        mut x: NonNull<MinHeapNode<T, A>>,
        mut y: NonNull<MinHeapNode<T, A>>,
    ) {
        if x == y {
            return;
        }

        let px = x.as_ref().parent;
        let py = y.as_ref().parent;

        if px == Some(y) {
            return self.swap_nodes(y, x);
        }

        let get_left = |n: NonNull<MinHeapNode<T, A>>| {
            n.as_ref()
                .link
                .left()
                .map(|v| NonNull::from_ref(MinHeapNode::node_of_link(v.as_ref())))
        };
        let get_right = |n: NonNull<MinHeapNode<T, A>>| {
            n.as_ref()
                .link
                .right()
                .map(|v| NonNull::from_ref(MinHeapNode::node_of_link(v.as_ref())))
        };
        let mut set_left = |mut p: NonNull<MinHeapNode<T, A>>,
                            n: Option<NonNull<MinHeapNode<T, A>>>| {
            p.as_mut()
                .link
                .set_left(n.map(|n| NonNull::from_ref(&n.as_ref().link)));
        };
        let mut set_right = |mut p: NonNull<MinHeapNode<T, A>>,
                             n: Option<NonNull<MinHeapNode<T, A>>>| {
            p.as_mut()
                .link
                .set_right(n.map(|n| NonNull::from_ref(&n.as_ref().link)));
        };

        let lx = get_left(x);
        let rx = get_right(x);

        let ly = get_left(y);
        let ry = get_right(y);

        let mut update_parent_child = |old_ptr: NonNull<MinHeapNode<T, A>>,
                                       new_ptr: NonNull<MinHeapNode<T, A>>,
                                       parent: Option<NonNull<MinHeapNode<T, A>>>|
         -> Option<(bool, NonNull<MinHeapNode<T, A>>)> {
            match parent {
                None => {
                    self.root = Some(new_ptr);
                    None
                }
                Some(mut p) => {
                    let is_left = if get_left(p) == Some(old_ptr) {
                        set_left(p, Some(new_ptr));
                        true
                    } else {
                        set_right(p, Some(new_ptr));
                        false
                    };
                    Some((is_left, p))
                }
            }
        };

        if py == Some(x) {
            update_parent_child(x, y, px);
            y.as_mut().parent = px;
            x.as_mut().parent = Some(y);

            if lx == Some(y) {
                set_left(y, Some(x));
                set_right(y, rx);
                if let Some(mut r) = rx {
                    r.as_mut().parent = Some(y);
                }
            } else {
                set_right(y, Some(x));
                set_left(y, lx);
                if let Some(mut l) = lx {
                    l.as_mut().parent = Some(y);
                }
            }

            set_left(x, ly);
            if let Some(mut l) = ly {
                l.as_mut().parent = Some(x);
            }
            set_right(x, ry);
            if let Some(mut r) = ry {
                r.as_mut().parent = Some(x);
            }
        } else {
            let maybe_left = update_parent_child(x, y, px);
            // Sibling case.
            if let Some((is_left, p)) = maybe_left
                && px == py
            {
                if is_left {
                    set_right(p, Some(x));
                } else {
                    set_left(p, Some(x));
                }
            } else {
                update_parent_child(y, x, py);
            }

            x.as_mut().parent = py;
            y.as_mut().parent = px;

            set_left(x, ly);
            if let Some(mut l) = ly {
                l.as_mut().parent = Some(x);
            }
            set_left(y, lx);
            if let Some(mut l) = lx {
                l.as_mut().parent = Some(y);
            }

            set_right(x, ry);
            if let Some(mut r) = ry {
                r.as_mut().parent = Some(x);
            }
            set_right(y, rx);
            if let Some(mut r) = rx {
                r.as_mut().parent = Some(y);
            }
        }
    }

    fn is_linked_in_heap(&self, node: NonNull<MinHeapNode<T, A>>) -> bool {
        if Some(node) == self.root {
            return true;
        }
        unsafe { node.as_ref().parent.is_some() }
    }

    fn inner_remove(&mut self, mut node: NonNull<MinHeapNode<T, A>>) {
        let mut path = (0, 0);
        let (last, last_parent) = self.node_at(self.size - 1, &mut path);
        let Some(mut last) = last else {
            panic!("Node should not be None when the index is valid")
        };
        let last_mut = unsafe { last.as_mut() };
        debug_assert!(last_mut.link.is_detached());
        unsafe { self.swap_nodes(node, last) };
        let node_mut = unsafe { node.as_mut() };
        debug_assert!(node_mut.link.is_detached());
        let node_parent = node_mut.parent.take();
        debug_assert!(node_mut.parent.is_none());
        self.size -= 1;
        let Some(mut last_parent) = last_parent else {
            let root = self.root.take();
            debug_assert_eq!(root, Some(node));
            debug_assert_eq!(last, node);
            return;
        };
        debug_assert!(path.0 > 0);
        let is_left = (1 << (path.0 - 1)) & path.1 == 0;
        let last_parent_mut = unsafe { last_parent.as_mut() };
        if node == last {
            debug_assert_eq!(Some(last_parent), node_parent);
            if is_left {
                last_parent_mut.link.set_left(None);
            } else {
                last_parent_mut.link.set_right(None);
            }
            return;
        }
        if node == last_parent {
            debug_assert_eq!(Some(last), node_parent);
            if is_left {
                last_mut.link.set_left(None);
            } else {
                last_mut.link.set_right(None);
            }
        } else {
            debug_assert_eq!(Some(last_parent), node_parent);
            if is_left {
                debug_assert_eq!(
                    last_parent_mut.link.left(),
                    Some(NonNull::from_mut(&mut node_mut.link))
                );
                last_parent_mut.link.set_left(None);
            } else {
                debug_assert_eq!(
                    last_parent_mut.link.right(),
                    Some(NonNull::from_mut(&mut node_mut.link))
                );
                last_parent_mut.link.set_right(None);
            }
        }
        let last_val = MinHeapNode::owner(last_mut);
        let Some(mut parent) = last_mut.parent else {
            debug_assert_eq!(self.root, Some(last));
            // self.swap_node should have set the self.root.
            self.top_down_adjust(last_val, last);
            return;
        };
        let parent_mut = unsafe { parent.as_mut() };
        let parent_val = MinHeapNode::owner(parent_mut);
        if (self.compare)(last_val, parent_val) == core::cmp::Ordering::Less {
            return self.bottom_up_adjust(last_val, last);
        }
        self.top_down_adjust(last_val, last)
    }

    pub fn remove<'a>(
        &mut self,
        mut iou: IouMinHeapNodeMut<'_, T, A>,
    ) -> Option<IouMinHeapNodeMut<'a, T, A>> {
        let Some(mut node) = iou.node else {
            panic!("Nil node")
        };
        if !self.is_linked_in_heap(node) {
            if !LinkType::detach(&mut unsafe { node.as_mut() }.link) {
                return None;
            }
            return Some(IouMinHeapNodeMut {
                node: None,
                _lt: PhantomData,
            });
        }
        self.inner_remove(node);
        Some(IouMinHeapNodeMut {
            node: None,
            _lt: PhantomData,
        })
    }

    pub fn is_active(&self, iou: &IouMinHeapNodeMut<'_, T, A>) -> bool {
        let Some(node) = iou.node else {
            return false;
        };
        self.is_linked_in_heap(node)
    }

    pub fn pop(&mut self) -> &mut Self {
        let Some(mut node) = self.root else {
            return self;
        };
        debug_assert!(self.is_linked_in_heap(node));
        self.inner_remove(node);
        debug_assert!(unsafe { node.as_ref() }.link.is_detached());
        debug_assert!(self.popped.prev.is_none());
        let ok = LinkType::insert_after(&mut self.popped, &mut unsafe { node.as_mut() }.link);
        debug_assert!(ok);
        debug_assert_eq!(
            self.popped.right(),
            Some(NonNull::from_ref(&unsafe { node.as_ref() }.link))
        );
        debug_assert_eq!(
            self.popped.next,
            Some(NonNull::from_ref(&unsafe { node.as_ref() }.link))
        );
        debug_assert_eq!(
            Some(NonNull::from_ref(&self.popped)),
            unsafe { node.as_ref() }.link.prev
        );
        self
    }

    pub fn peek(&self) -> Option<&T> {
        let root = self.root?;
        Some(MinHeapNode::owner(unsafe { root.as_ref() }))
    }

    pub fn for_each_popped_value<F>(&mut self, f: F)
    where
        F: Fn(&mut T),
    {
        let mut it = LinkTypeIterator::new(&self.popped, None);
        for mut node in it {
            let node_mut = unsafe { node.as_mut() };
            debug_assert_ne!(node_mut.left(), Some(node));
            debug_assert_ne!(node_mut.right(), Some(node));
            let val = unsafe { LinkType::owner_mut(node_mut) };
            f(val);
        }
    }

    pub fn move_chosen_popped_values_to_heap<F>(&mut self, choose: F) -> usize
    where
        F: Fn(&T) -> bool,
    {
        let mut chosen = 0;
        let mut it = LinkTypeIterator::new(&self.popped, None);
        for mut node in it {
            debug_assert!(!self.is_linked_in_heap(unsafe {
                NonNull::from_ref(MinHeapNode::node_of_link(node.as_ref()))
            }));
            let val = unsafe { LinkType::owner_mut(node.as_mut()) };
            if !choose(val) {
                continue;
            }
            LinkType::detach(unsafe { node.as_mut() });
            debug_assert!(unsafe { node.as_mut() }.is_detached());
            chosen += 1;
            self.push(val);
        }
        chosen
    }

    pub fn validate(&self) {
        let size = self.size();
        for i in 0..size {
            let mut path = (0, 0);
            let (current, current_parent) = self.node_at(i, &mut path);
            assert!(current.is_some());
            let current_mut = unsafe { current.unwrap().as_mut() };
            if 2 * i + 1 >= size {
                unsafe { assert!(current_mut.link.left().is_none()) };
            }
            if 2 * i + 2 >= size {
                unsafe { assert!(current_mut.link.right().is_none()) };
            }
            assert_eq!(current_mut.parent, current_parent);
            if path.0 == 0 {
                assert!(current_parent.is_none());
                assert_eq!(self.root, current);
                continue;
            }
            assert!(current_parent.is_some());
            let is_left = 1 << (path.0 - 1) & path.1 == 0;
            let parent_ref = unsafe { current_parent.unwrap().as_ref() };
            let parent_val = MinHeapNode::owner(parent_ref);
            let current_val = MinHeapNode::owner(current_mut);
            let order = (self.compare)(parent_val, current_val);
            assert!(order == core::cmp::Ordering::Less || order == core::cmp::Ordering::Equal);
            if is_left {
                assert_eq!(
                    parent_ref.link.left(),
                    Some(NonNull::from_ref(&current_mut.link))
                );
            } else {
                assert_eq!(
                    parent_ref.link.right(),
                    Some(NonNull::from_ref(&current_mut.link))
                );
            }
        }
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
        let root = heap.peek();
        assert!(root.is_some());
        assert_eq!(root.unwrap().val, 42);
        let mut n1 = Box::new(Foo {
            node: MinHeapNode::new(),
            val: 37,
        });
        heap.push(&mut n1);
        assert_eq!(heap.size(), 2);
        let root = heap.peek();
        assert!(root.is_some());
        assert_eq!(root.unwrap().val, 37);
        let mut n2 = Box::new(Foo {
            node: MinHeapNode::new(),
            val: 43,
        });
        heap.push(&mut n2);
        assert_eq!(heap.size(), 3);
        let root = heap.peek();
        assert!(root.is_some());
        assert_eq!(root.unwrap().val, 37);
        let mut n3 = Box::new(Foo {
            node: MinHeapNode::new(),
            val: 23,
        });
        heap.push(&mut n3);
        assert_eq!(heap.size(), 4);
        let root = heap.peek();
        assert!(root.is_some());
        assert_eq!(root.unwrap().val, 23);
    }

    #[test]
    fn test_removal() {
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
        let iou2 = heap.push(&mut n2).unwrap();
        heap.validate();
        let iou1 = heap.push(&mut n1).unwrap();
        heap.validate();
        let iou0 = heap.push(&mut n0).unwrap();
        heap.validate();
        assert_eq!(heap.size(), 3);
        assert_eq!(heap.peek().unwrap().val, 0);
        let iou3 = unsafe { IouMinHeapNodeMut::from_mut(&mut *n3) };
        assert!(heap.remove(iou3).is_none());
        assert_eq!(heap.size(), 3);
        assert_eq!(heap.peek().unwrap().val, 0);
        heap.validate();
        heap.remove(iou0);
        heap.validate();
        assert_eq!(heap.size(), 2);
        assert_eq!(heap.peek().unwrap().val, 1);
        heap.remove(iou2);
        heap.validate();
        assert_eq!(heap.peek().unwrap().val, 1);
        let mut n3 = Box::new(Foo {
            node: MinHeapNode::new(),
            val: 3,
        });
        heap.validate();
        let iou3 = heap.push(&mut n3).unwrap();
        assert_eq!(heap.size(), 2);
        assert_eq!(heap.peek().unwrap().val, 1);
        heap.pop();
        assert_eq!(heap.size(), 1);
        heap.validate();
        heap.pop();
        heap.validate();
        assert_eq!(heap.size(), 0);
        heap.validate();
        heap.remove(iou1);
        heap.validate();
        heap.remove(iou3);
        heap.validate();
    }

    #[test]
    fn test_stack_removal() {
        let mut heap = MinHeap::<Foo, Node, _>::new(|l, r| l.val.cmp(&r.val).reverse());
        {
            let mut n0 = Foo {
                node: MinHeapNode::new(),
                val: 0,
            };
            let b0 = heap.push(&mut n0).unwrap();
            let mut n1 = Foo {
                node: MinHeapNode::new(),
                val: 1,
            };
            let b1 = heap.push(&mut n1).unwrap();
            let mut n2 = Foo {
                node: MinHeapNode::new(),
                val: 2,
            };
            let b2 = heap.push(&mut n2).unwrap();
            let mut n3 = Foo {
                node: MinHeapNode::new(),
                val: 3,
            };
            let b3 = heap.push(&mut n3).unwrap();
            let mut n4 = Foo {
                node: MinHeapNode::new(),
                val: 4,
            };
            let b4 = heap.push(&mut n4).unwrap();
            let mut n5 = Foo {
                node: MinHeapNode::new(),
                val: 5,
            };
            let b5 = heap.push(&mut n5).unwrap();
            assert_eq!(heap.peek().unwrap().val, 5);
            heap.remove(b3);
            assert_eq!(heap.peek().unwrap().val, 5);
            heap.remove(b5);
            assert_eq!(heap.peek().unwrap().val, 4);
            heap.remove(b2);
            assert_eq!(heap.peek().unwrap().val, 4);
            heap.remove(b4);
            assert_eq!(heap.peek().unwrap().val, 1);
            heap.remove(b0);
            assert_eq!(heap.peek().unwrap().val, 1);
            heap.remove(b1);
            assert!(heap.peek().is_none());
        }
    }

    #[test]
    fn test_remove_sibling() {
        let mut heap = MinHeap::<Foo, Node, _>::new(|l, r| l.val.cmp(&r.val));
        let mut n0 = Foo {
            node: MinHeapNode::new(),
            val: 0,
        };
        let mut n1 = Foo {
            node: MinHeapNode::new(),
            val: 1,
        };
        let mut n2 = Foo {
            node: MinHeapNode::new(),
            val: 2,
        };
        heap.push(&mut n0);
        let iou1 = heap.push(&mut n1).unwrap();
        heap.push(&mut n2);
        heap.validate();
        heap.remove(iou1);
    }

    #[bench]
    fn bench_push_and_pop(b: &mut Bencher) {
        b.iter(|| {
            let mut heap = MinHeap::<Foo, Node, _>::new(|l, r| l.val.cmp(&r.val).reverse());
            let mut n0 = Foo {
                node: MinHeapNode::new(),
                val: 0,
            };
            let mut n1 = Foo {
                node: MinHeapNode::new(),
                val: 1,
            };
            let mut n2 = Foo {
                node: MinHeapNode::new(),
                val: 2,
            };
            let mut n3 = Foo {
                node: MinHeapNode::new(),
                val: 3,
            };
            heap.push(&mut n0);
            heap.push(&mut n1);
            heap.push(&mut n2);
            heap.push(&mut n3);
            debug_assert_eq!(heap.peek().unwrap().val, 3);
            let size = heap.size();
            debug_assert_eq!(size, 4);
            for _i in 0..size {
                heap.pop();
            }
        });
    }

    #[bench]
    fn bench_push_and_pop_std_heap(b: &mut Bencher) {
        use std::collections::BinaryHeap;
        #[derive(Eq, Ord, PartialEq, PartialOrd)]
        struct Foo {
            val: usize,
        };
        b.iter(|| {
            let mut heap = BinaryHeap::new();
            heap.push(0);
            heap.push(1);
            heap.push(2);
            heap.push(3);
            debug_assert_eq!(*heap.peek().unwrap(), 3);
            let size = heap.len();
            debug_assert_eq!(size, 4);
            for _i in 0..size {
                heap.pop();
            }
        });
    }

    #[bench]
    fn bench_push_and_pop_std_btree(b: &mut Bencher) {
        use std::collections::BTreeSet;
        #[derive(Eq, Ord, PartialEq, PartialOrd)]
        struct Foo {
            val: usize,
        };
        b.iter(|| {
            let mut heap = BTreeSet::new();
            heap.insert(0);
            heap.insert(1);
            heap.insert(2);
            heap.insert(3);
            let size = heap.len();
            debug_assert_eq!(size, 4);
            for _i in 0..size {
                heap.pop_first();
            }
        });
    }

    #[test]
    fn fuzz() {
        let mut iheap = MinHeap::<Foo, Node, _>::new(|l, r| l.val.cmp(&r.val).reverse());
        let mut vec = Vec::new();
        for i in 0..11 {
            vec.push(Foo {
                node: MinHeapNode::new(),
                val: i,
            });
        }
        iheap.push(&mut vec[0]);
        iheap.validate();
        iheap.push(&mut vec[2]);
        iheap.validate();
        iheap.push(&mut vec[4]);
        iheap.validate();
        iheap.push(&mut vec[6]);
        iheap.validate();
        iheap.push(&mut vec[8]);
        iheap.validate();
        iheap.push(&mut vec[10]);
        iheap.validate();
        iheap.remove(unsafe { IouMinHeapNodeMut::from_mut(&mut vec[0]) });
        iheap.validate();
        iheap.push(&mut vec[1]);
        iheap.validate();
        iheap.remove(unsafe { IouMinHeapNodeMut::from_mut(&mut vec[2]) });
        iheap.validate();
        iheap.push(&mut vec[3]);
        iheap.validate();
        iheap.remove(unsafe { IouMinHeapNodeMut::from_mut(&mut vec[4]) });
        iheap.validate();
        iheap.push(&mut vec[5]);
        iheap.validate();
        iheap.remove(unsafe { IouMinHeapNodeMut::from_mut(&mut vec[6]) });
        iheap.validate();
    }

    #[test]
    fn fuzz1() {
        let mut iheap = MinHeap::<Foo, Node, _>::new(|l, r| l.val.cmp(&r.val).reverse());
        let mut vec = Vec::new();
        for i in 0..4 {
            vec.push(Foo {
                node: MinHeapNode::new(),
                val: i,
            });
        }
        for i in 0..3 {
            for f in vec.iter_mut() {
                if f.val % 2 == i % 2 {
                    iheap.validate();
                    iheap.push(f);
                    iheap.validate();
                } else {
                    iheap.validate();
                    iheap.remove(unsafe { IouMinHeapNodeMut::from_mut(f) });
                    iheap.validate();
                }
            }
        }
    }

    #[test]
    fn fuzz2() {
        let mut iheap = MinHeap::<Foo, Node, _>::new(|l, r| l.val.cmp(&r.val).reverse());
        let mut vec = Vec::new();
        for i in 0..1 << 10 {
            vec.push(Foo {
                node: MinHeapNode::new(),
                val: i,
            });
        }
        for i in 0..3 {
            for f in vec.iter_mut() {
                if f.val % 2 == i % 2 {
                    iheap.validate();
                    iheap.push(f);
                    iheap.validate();
                } else {
                    iheap.validate();
                    iheap.remove(unsafe { IouMinHeapNodeMut::from_mut(f) });
                    iheap.validate();
                }
            }
        }
    }

    #[test]
    fn concurrent_stress() {
        use crate::{tinyarc::TinyArc as Arc, tinyrwlock::RwLock};
        let num_cores = std::thread::available_parallelism().unwrap();
        let scratch = MinHeap::<Foo, Node, _>::new(|l, r| l.val.cmp(&r.val).reverse());
        let iheap = Arc::new(RwLock::new(scratch));
        let mut vec = Arc::new(RwLock::new(Vec::new()));
        {
            let mut vec_mut = vec.write();
            for i in 0..1 << 10 {
                vec_mut.push(Foo {
                    node: MinHeapNode::new(),
                    val: i,
                });
            }
        }
        let closure = {
            let iheap = iheap.clone();
            let vec = vec.clone();
            move || {
                {
                    let mut vec_mut = vec.write();
                    for f in vec_mut.iter_mut() {
                        iheap.write().push(f);
                    }
                }
                {
                    let mut vec_mut = vec.write();
                    for f in vec_mut.iter_mut() {
                        let iou = unsafe { IouMinHeapNodeMut::from_mut(f) };
                        iheap.write().remove(iou);
                    }
                }
            }
        };
        let mut handles = vec![];
        for i in 0..num_cores.into() {
            let handle = std::thread::spawn(closure.clone());
            handles.push(handle);
        }
        for handle in handles {
            handle.join().expect("Thread panicked");
        }
    }
}
