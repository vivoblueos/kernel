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

use crate::{intrusive::Adapter, tinyarc::TinyArc};
use core::{cmp::Ordering, marker::PhantomData, ops::Drop, ptr::NonNull};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Color {
    Red = 0,
    Black = 1,
}

const COLOR_MASK: usize = 1;
const PTR_MASK: usize = !COLOR_MASK;

#[derive(Debug)]
#[repr(C, align(2))]
pub struct RBLink {
    tagged_parent_ptr: usize,

    left: Option<NonNull<RBLink>>,
    right: Option<NonNull<RBLink>>,
}
impl RBLink {
    pub const fn new() -> Self {
        Self {
            tagged_parent_ptr: 0,
            left: None,
            right: None,
        }
    }

    #[inline]
    pub fn color(&self) -> Color {
        if (self.tagged_parent_ptr & COLOR_MASK) == 0 {
            Color::Red
        } else {
            Color::Black
        }
    }
    #[inline]
    pub fn set_color(&mut self, color: Color) {
        let bit = color as usize;
        self.tagged_parent_ptr = (self.tagged_parent_ptr & PTR_MASK) | bit;
    }
    #[inline]
    pub fn is_red(&self) -> bool {
        self.color() == Color::Red
    }
    #[inline]
    pub fn is_black(&self) -> bool {
        self.color() == Color::Black
    }
    #[inline]
    pub fn parent(&self) -> Option<NonNull<RBLink>> {
        let ptr = (self.tagged_parent_ptr & PTR_MASK) as *mut RBLink;
        NonNull::new(ptr)
    }
    #[inline]
    pub fn set_parent(&mut self, parent: Option<NonNull<RBLink>>) {
        let ptr_val = match parent {
            Some(p) => p.as_ptr() as usize,
            None => 0,
        };

        debug_assert_eq!(ptr_val & COLOR_MASK, 0, "Pointer not aligned!");

        let current_color = self.tagged_parent_ptr & COLOR_MASK;
        self.tagged_parent_ptr = ptr_val | current_color;
    }
}

pub struct RBTree<T, A: Adapter<T>> {
    root: Option<NonNull<RBLink>>,
    size: usize,
    _marker: PhantomData<(T, A)>,
}

unsafe impl<T: Send + Sync, A: Adapter<T>> Send for RBTree<T, A> {}
unsafe impl<T: Send + Sync, A: Adapter<T>> Sync for RBTree<T, A> {}

impl<T, A: Adapter<T>> RBTree<T, A> {
    pub fn new() -> Self {
        Self {
            root: None,
            size: 0,
            _marker: PhantomData,
        }
    }

    unsafe fn get_link(&self, object: *mut T) -> NonNull<RBLink> {
        unsafe {
            let ptr = (object as *mut u8).add(A::offset()) as *mut RBLink;
            NonNull::new_unchecked(ptr)
        }
    }

    pub unsafe fn get_obj(&self, link: NonNull<RBLink>) -> *mut T {
        unsafe { (link.as_ptr() as *mut u8).sub(A::offset()) as *mut T }
    }

    pub fn search<K, F>(&self, key: &K, compare: F) -> Option<&T>
    where
        F: Fn(&K, &T) -> Ordering,
    {
        unsafe {
            let mut current = self.root;
            while let Some(node) = current {
                let node_ref = node.as_ref();
                let obj = self.get_obj(node);
                match compare(key, &*obj) {
                    Ordering::Equal => return Some(&*obj),
                    Ordering::Less => current = node_ref.left,
                    Ordering::Greater => current = node_ref.right,
                }
            }
        }
        None
    }

    pub fn insert<F>(&mut self, object: TinyArc<T>, compare: F)
    where
        F: Fn(&T, &T) -> core::cmp::Ordering,
    {
        let object_ptr = TinyArc::into_raw(object) as *mut T;
        unsafe {
            let mut new_link = self.get_link(object_ptr);

            {
                let node = new_link.as_mut();
                node.left = None;
                node.right = None;
                node.set_color(Color::Red);
            }
            let mut y = None;
            let mut x = self.root;
            while let Some(node) = x {
                y = Some(node);
                let obj = self.get_obj(node);
                match compare(&*object_ptr, &*obj) {
                    Ordering::Less => x = node.as_ref().left,
                    Ordering::Greater => x = node.as_ref().right,
                    Ordering::Equal => {
                        let _ = TinyArc::from_raw(object_ptr);
                        return;
                    }
                }
            }

            new_link.as_mut().set_parent(y);
            if y.is_none() {
                self.root = Some(new_link);
            } else {
                let mut y_ptr = y.unwrap();
                let y_obj = self.get_obj(y_ptr);
                let y_mut = y_ptr.as_mut();

                match compare(&*object_ptr, &*y_obj) {
                    Ordering::Less => y_mut.left = Some(new_link),
                    _ => y_mut.right = Some(new_link),
                }
            }
            self.size += 1;
            self.fix_after_insertion(new_link);
        }
    }

    unsafe fn fix_after_insertion(&mut self, mut z: NonNull<RBLink>) {
        while let Some(mut parent) = z.as_ref().parent() {
            if !parent.as_ref().is_red() {
                break;
            }

            let mut grandparent = parent.as_ref().parent().unwrap_unchecked();
            let is_parent_left = grandparent.as_ref().left == Some(parent);
            let uncle = if is_parent_left {
                grandparent.as_ref().right
            } else {
                grandparent.as_ref().left
            };
            // Case 1: Uncle is Red
            if let Some(mut uncle_node) = uncle {
                if uncle_node.as_ref().is_red() {
                    parent.as_mut().set_color(Color::Black);
                    uncle_node.as_mut().set_color(Color::Black);
                    grandparent.as_mut().set_color(Color::Red);
                    z = grandparent;
                    continue;
                }
            }
            // Case 2 & 3: Uncle is Black (or None)
            let is_z_left = parent.as_ref().left == Some(z);
            if is_parent_left {
                if !is_z_left {
                    // Case 2: Triangle shape (Left-Right) -> Rotate Left
                    self.rotate_left(parent);
                    z = parent;
                    parent = z.as_ref().parent().unwrap_unchecked();
                }
                // Case 3: Line shape (Left-Left) -> Rotate Right
                parent.as_mut().set_color(Color::Black);
                grandparent.as_mut().set_color(Color::Red);
                self.rotate_right(grandparent);
            } else {
                if is_z_left {
                    // Case 2: Triangle shape (Right-Left) -> Rotate Right
                    self.rotate_right(parent);
                    z = parent;
                    parent = z.as_ref().parent().unwrap_unchecked();
                }
                // Case 3: Line shape (Right-Right) -> Rotate Left
                parent.as_mut().set_color(Color::Black);
                grandparent.as_mut().set_color(Color::Red);
                self.rotate_left(grandparent);
            }
        }

        // Sometime we changed color of root.
        if let Some(mut root) = self.root {
            root.as_mut().set_color(Color::Black);
        }
    }
    unsafe fn rotate_left(&mut self, mut x: NonNull<RBLink>) {
        unsafe {
            let mut y = x.as_ref().right.expect("Rotate left expects right child");

            x.as_mut().right = y.as_ref().left;
            if let Some(mut beta) = y.as_ref().left {
                beta.as_mut().set_parent(Some(x));
            }

            let p = x.as_ref().parent();
            y.as_mut().set_parent(p);
            if p.is_none() {
                self.root = Some(y);
            } else {
                let mut p_node = p.unwrap();
                if p_node.as_ref().left == Some(x) {
                    p_node.as_mut().left = Some(y);
                } else {
                    p_node.as_mut().right = Some(y);
                }
            }
            y.as_mut().left = Some(x);
            x.as_mut().set_parent(Some(y));
        }
    }

    unsafe fn rotate_right(&mut self, mut x: NonNull<RBLink>) {
        unsafe {
            let mut y = x.as_ref().left.expect("Rotate right expects left child");

            x.as_mut().left = y.as_ref().right;
            if let Some(mut beta) = y.as_ref().right {
                beta.as_mut().set_parent(Some(x));
            }

            let p = x.as_ref().parent();
            y.as_mut().set_parent(p);
            if p.is_none() {
                self.root = Some(y);
            } else {
                let mut p_node = p.unwrap();
                if p_node.as_ref().right == Some(x) {
                    p_node.as_mut().right = Some(y);
                } else {
                    p_node.as_mut().left = Some(y);
                }
            }

            y.as_mut().right = Some(x);
            x.as_mut().set_parent(Some(y));
        }
    }

    pub fn remove<K, F>(&mut self, key: &K, compare: F) -> Option<TinyArc<T>>
    where
        F: Fn(&K, &T) -> Ordering,
    {
        unsafe {
            let mut current = self.root;
            while let Some(node) = current {
                let node_ref = node.as_ref();
                let obj = self.get_obj(node);
                match compare(key, &*obj) {
                    Ordering::Equal => {
                        // Delete node from tree after finding it.
                        self.delete_node(node);
                        self.size -= 1;
                        // Key Point: give back ownership.
                        return Some(TinyArc::from_raw(obj));
                    }
                    Ordering::Less => current = node_ref.left,
                    Ordering::Greater => current = node_ref.right,
                }
            }
        }
        None
    }

    unsafe fn delete_node(&mut self, mut z: NonNull<RBLink>) {
        unsafe {
            let mut y = z;
            let mut y_original_color = y.as_ref().color();
            let x: Option<NonNull<RBLink>>;
            let x_parent: Option<NonNull<RBLink>>;
            //Case 1. z has no more than one child node.
            if z.as_ref().left.is_none() {
                x = z.as_ref().right;
                x_parent = z.as_ref().parent();
                self.transplant(z, z.as_ref().right);
            } else if z.as_ref().right.is_none() {
                x = z.as_ref().left;
                x_parent = z.as_ref().parent();
                self.transplant(z, z.as_ref().left);
            } else {
                //Case 2. z is internal node.
                let z_right = z.as_ref().right.unwrap();
                y = self.minimum(z_right);
                y_original_color = y.as_ref().color();
                x = y.as_ref().right;
                if y.as_ref().parent() == Some(z) {
                    x_parent = Some(y);
                } else {
                    x_parent = y.as_ref().parent();
                    self.transplant(y, y.as_ref().right);
                    y.as_mut().right = z.as_ref().right;
                    if let Some(mut yr) = y.as_ref().right {
                        yr.as_mut().set_parent(Some(y));
                    }
                }
                self.transplant(z, Some(y));
                y.as_mut().left = z.as_ref().left;
                if let Some(mut yl) = y.as_ref().left {
                    yl.as_mut().set_parent(Some(y));
                }
                y.as_mut().set_color(z.as_ref().color());
            }
            if y_original_color == Color::Black {
                self.fix_after_deletion(x, x_parent);
            }

            let z_mut = z.as_mut();
            z_mut.left = None;
            z_mut.right = None;
            z_mut.tagged_parent_ptr = 0;
        }
    }

    unsafe fn fix_after_deletion(
        &mut self,
        mut x: Option<NonNull<RBLink>>,
        mut parent: Option<NonNull<RBLink>>,
    ) {
        unsafe {
            // w is silbling of x.
            while x != self.root && (x.is_none() || x.unwrap().as_ref().is_black()) {
                if parent.is_none() {
                    break;
                }
                let mut p_node = parent.unwrap();

                let is_x_left = x == p_node.as_ref().left;

                let mut w = if is_x_left {
                    p_node.as_ref().right
                } else {
                    p_node.as_ref().left
                };
                if w.is_none() {
                    x = parent;
                    parent = x.unwrap().as_ref().parent();
                    continue;
                }
                let mut w_node = w.unwrap();
                // Case 1: Sibling w is Red
                if w_node.as_ref().is_red() {
                    w_node.as_mut().set_color(Color::Black);
                    p_node.as_mut().set_color(Color::Red);
                    if is_x_left {
                        self.rotate_left(p_node);
                        w = p_node.as_ref().right;
                    } else {
                        self.rotate_right(p_node);
                        w = p_node.as_ref().left;
                    }
                    w_node = w.unwrap();
                }
                // w is Black now.
                let left_child = w_node.as_ref().left;
                let right_child = w_node.as_ref().right;
                let left_black = left_child.map_or(true, |n| n.as_ref().is_black());
                let right_black = right_child.map_or(true, |n| n.as_ref().is_black());
                // Case 2: Sibling w's children are both Black
                if left_black && right_black {
                    w_node.as_mut().set_color(Color::Red);
                    x = parent;
                    parent = x.unwrap().as_ref().parent();
                } else {
                    if is_x_left {
                        // Case 3: w is black, w.left is red, w.right is black.
                        if right_black {
                            if let Some(mut l) = left_child {
                                l.as_mut().set_color(Color::Black);
                            }
                            w_node.as_mut().set_color(Color::Red);
                            self.rotate_right(w_node);
                            w = p_node.as_ref().right;
                            w_node = w.unwrap();
                        }
                        // Case 4: w is black, w.right is red.
                        w_node.as_mut().set_color(p_node.as_ref().color());
                        p_node.as_mut().set_color(Color::Black);
                        if let Some(mut r) = w_node.as_ref().right {
                            r.as_mut().set_color(Color::Black);
                        }
                        self.rotate_left(p_node);
                        x = self.root;
                    } else {
                        // Mirror Case 3
                        if left_black {
                            if let Some(mut r) = right_child {
                                r.as_mut().set_color(Color::Black);
                            }
                            w_node.as_mut().set_color(Color::Red);
                            self.rotate_left(w_node);
                            w = p_node.as_ref().left;
                            w_node = w.unwrap();
                        }
                        // Mirror Case 4
                        w_node.as_mut().set_color(p_node.as_ref().color());
                        p_node.as_mut().set_color(Color::Black);
                        if let Some(mut l) = w_node.as_ref().left {
                            l.as_mut().set_color(Color::Black);
                        }
                        self.rotate_right(p_node);
                        x = self.root;
                    }
                }
            }
            if let Some(mut x_node) = x {
                x_node.as_mut().set_color(Color::Black);
            }
        }
    }

    unsafe fn transplant(&mut self, u: NonNull<RBLink>, v: Option<NonNull<RBLink>>) {
        unsafe {
            let p = u.as_ref().parent();
            if p.is_none() {
                self.root = v;
            } else {
                let mut p_node = p.unwrap();
                if Some(u) == p_node.as_ref().left {
                    p_node.as_mut().left = v;
                } else {
                    p_node.as_mut().right = v;
                }
            }
            if let Some(mut v_node) = v {
                v_node.as_mut().set_parent(p);
            }
        }
    }

    pub fn minimum(&self, mut node: NonNull<RBLink>) -> NonNull<RBLink> {
        unsafe {
            while let Some(left) = node.as_ref().left {
                node = left;
            }
            node
        }
    }

    pub fn iter(&self) -> RBIterator<'_, T, A> {
        RBIterator::new(self)
    }

    pub fn print_structure(&self)
    where
        T: std::fmt::Debug,
    {
        unsafe {
            self.print_node(self.root, 0);
        }
    }

    unsafe fn print_node(&self, node: Option<NonNull<RBLink>>, depth: usize)
    where
        T: std::fmt::Debug,
    {
        unsafe {
            if let Some(n) = node {
                self.print_node(n.as_ref().right, depth + 1);
                let indent = "    ".repeat(depth);
                let obj = self.get_obj(n);
                let color = if n.as_ref().is_red() { "RED" } else { "BLK" };
                println!("{}Node ({})", indent, color);
                self.print_node(n.as_ref().left, depth + 1);
            }
        }
    }
}

pub struct RBIterator<'a, T, A: Adapter<T>> {
    tree: &'a RBTree<T, A>,
    stack: Vec<NonNull<RBLink>>,
}

impl<'a, T, A: Adapter<T>> RBIterator<'a, T, A> {
    pub fn new(tree: &'a RBTree<T, A>) -> Self {
        let mut iter = Self {
            tree,
            stack: Vec::new(),
        };
        unsafe {
            iter.push_left(tree.root);
        }
        iter
    }
    unsafe fn push_left(&mut self, mut node: Option<NonNull<RBLink>>) {
        unsafe {
            while let Some(n) = node {
                self.stack.push(n);
                node = n.as_ref().left;
            }
        }
    }
}

impl<'a, T, A: Adapter<T>> Iterator for RBIterator<'a, T, A> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            let node = self.stack.pop()?;
            let right = node.as_ref().right;
            if right.is_some() {
                self.push_left(right);
            }
            let obj_ptr = self.tree.get_obj(node);
            Some(&*obj_ptr)
        }
    }
}

impl<T, A: Adapter<T>> Drop for RBTree<T, A> {
    fn drop(&mut self) {
        while let Some(root) = self.root {
            unsafe {
                let obj_ptr = self.get_obj(root);
                self.delete_node(root);
                let _ = TinyArc::from_raw(obj_ptr);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    extern crate test;
    use super::{TinyArc, *};
    use std::{
        ptr::NonNull,
        string::{String, ToString},
        time::{Duration, Instant},
        vec::Vec,
    };
    use test::{black_box, Bencher};
    #[derive(Debug)]
    #[repr(C)]
    struct MyNode {
        key: i32,
        value: String,
        link: RBLink,
    }
    impl MyNode {
        fn new(key: i32, value: &str) -> Self {
            Self {
                key,
                value: value.to_string(),
                link: RBLink::new(),
            }
        }
    }
    crate::impl_simple_intrusive_adapter!(MyNodeAdapter, MyNode, link);
    unsafe fn check_rb_properties(tree: &RBTree<MyNode, MyNodeAdapter>) {
        if tree.root.is_none() {
            return;
        }
        unsafe {
            assert!(tree.root.unwrap().as_ref().is_black(), "Root must be black");
            check_node_properties(tree, tree.root);
        }
    }
    unsafe fn check_node_properties(
        tree: &RBTree<MyNode, MyNodeAdapter>,
        node: Option<NonNull<RBLink>>,
    ) -> usize {
        unsafe {
            match node {
                None => 1,
                Some(n) => {
                    let n_ref = n.as_ref();
                    let left = n_ref.left;
                    let right = n_ref.right;
                    if n_ref.is_red() {
                        if let Some(l) = left {
                            assert!(l.as_ref().is_black(), "Red node has red left child");
                        }
                        if let Some(r) = right {
                            assert!(r.as_ref().is_black(), "Red node has red right child");
                        }
                    }
                    let left_bh = check_node_properties(tree, left);
                    let right_bh = check_node_properties(tree, right);
                    assert_eq!(left_bh, right_bh, "Black height mismatch at node");
                    if n_ref.is_black() {
                        left_bh + 1
                    } else {
                        left_bh
                    }
                }
            }
        }
    }
    #[test]
    fn test_insert_and_search() {
        let mut tree = RBTree::<MyNode, MyNodeAdapter>::new();
        let cmp = |a: &MyNode, b: &MyNode| a.key.cmp(&b.key);
        let search_cmp = |k: &i32, n: &MyNode| k.cmp(&n.key);

        let n1 = TinyArc::new(MyNode::new(10, "Ten"));
        let n2 = TinyArc::new(MyNode::new(5, "Five"));
        let n3 = TinyArc::new(MyNode::new(20, "Twenty"));

        tree.insert(n1.clone(), cmp);
        tree.insert(n2.clone(), cmp);
        tree.insert(n3.clone(), cmp);

        unsafe {
            check_rb_properties(&tree);
        }
        assert_eq!(tree.size, 3);
        let res = tree.search(&10, search_cmp);
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, "Ten");
        let res = tree.search(&99, search_cmp);
        assert!(res.is_none());
    }
    #[test]
    fn test_delete_complex() {
        let mut tree = RBTree::<MyNode, MyNodeAdapter>::new();
        let cmp = |a: &MyNode, b: &MyNode| a.key.cmp(&b.key);
        let search_cmp = |k: &i32, n: &MyNode| k.cmp(&n.key);

        let mut keys = Vec::new();
        for i in 0..20 {
            let node = TinyArc::new(MyNode::new(i, "Val"));
            keys.push(i);
            tree.insert(node, cmp);
        }
        unsafe {
            check_rb_properties(&tree);
        }
        assert_eq!(tree.size, 20);

        for i in (0..20).step_by(2) {
            let key = keys[i as usize];
            let removed = tree.remove(&key, search_cmp);
            assert!(removed.is_some());
            unsafe {
                check_rb_properties(&tree);
            }
        }
        assert_eq!(tree.size, 10);
    }

    #[test]
    fn test_iterator() {
        let mut tree = RBTree::<MyNode, MyNodeAdapter>::new();
        let cmp = |a: &MyNode, b: &MyNode| a.key.cmp(&b.key);

        let nodes = [
            TinyArc::new(MyNode::new(3, "C")),
            TinyArc::new(MyNode::new(1, "A")),
            TinyArc::new(MyNode::new(2, "B")),
            TinyArc::new(MyNode::new(4, "D")),
        ];
        for p in &nodes {
            tree.insert(p.clone(), cmp);
        }

        let mut iter = tree.iter();
        assert_eq!(iter.next().unwrap().key, 1);
        assert_eq!(iter.next().unwrap().key, 2);
        assert_eq!(iter.next().unwrap().key, 3);
        assert_eq!(iter.next().unwrap().key, 4);
        assert!(iter.next().is_none());
    }
    #[test]
    fn test_sequential_insert_stress() {
        let mut tree = RBTree::<MyNode, MyNodeAdapter>::new();
        let cmp = |a: &MyNode, b: &MyNode| a.key.cmp(&b.key);
        let count = 2000;

        for i in 0..count {
            let val_str = format!("Val-{}", i);
            let node = TinyArc::new(MyNode::new(i, &val_str));
            tree.insert(node, cmp);
        }
        assert_eq!(tree.size, count as usize);
        unsafe {
            check_rb_properties(&tree);
        }
        let mut i = 0;
        for node in tree.iter() {
            assert_eq!(node.key, i);
            assert_eq!(node.value, format!("Val-{}", i));
            i += 1;
        }
        assert_eq!(i, count);
    }
    #[test]
    fn test_delete_root_scenarios() {
        let mut tree = RBTree::<MyNode, MyNodeAdapter>::new();
        let cmp = |a: &MyNode, b: &MyNode| a.key.cmp(&b.key);
        let search_cmp = |k: &i32, n: &MyNode| k.cmp(&n.key);
        // Scenario 1: Root only
        let n1 = TinyArc::new(MyNode::new(10, "Root"));
        tree.insert(n1.clone(), cmp);
        tree.remove(&10, search_cmp);
        assert_eq!(tree.size, 0);
        assert!(tree.root.is_none());
        // Scenario 2: Root + Left
        let n1 = TinyArc::new(MyNode::new(10, "Root"));
        let n2 = TinyArc::new(MyNode::new(5, "Left"));
        tree.insert(n1.clone(), cmp);
        tree.insert(n2.clone(), cmp);

        tree.remove(&10, search_cmp); // Remove Root
        assert_eq!(tree.size, 1);
        //Root isn't exposed
        assert!(tree.search(&5, search_cmp).is_some());

        tree.remove(&5, search_cmp); // Remove Left
                                     // Scenario 3: Root + Right
        let n1 = TinyArc::new(MyNode::new(10, "Root"));
        let n2 = TinyArc::new(MyNode::new(15, "Right"));
        tree.insert(n1.clone(), cmp);
        tree.insert(n2.clone(), cmp);
        tree.remove(&10, search_cmp);
        assert_eq!(tree.size, 1);
        assert!(tree.search(&15, search_cmp).is_some());
    }
    #[test]
    fn test_clrs_13_4_3() {
        let mut tree = RBTree::<MyNode, MyNodeAdapter>::new();
        let cmp = |a: &MyNode, b: &MyNode| a.key.cmp(&b.key);
        let search_cmp = |k: &i32, n: &MyNode| k.cmp(&n.key);

        let nodes = [41, 38, 31, 12, 19, 8];
        for &val in &nodes {
            let node = TinyArc::new(MyNode::new(val, "Val"));
            tree.insert(node, cmp);

            let delete_order = [8, 12, 19, 31, 38, 41];
            for &val in &delete_order {
                tree.remove(&val, search_cmp);
            }
            assert_eq!(tree.size, 0);
        }
    }
    #[bench]
    fn bench_admin_suite(_b: &mut Bencher) {
        println!("\n===Benchmark Start (TinyArc Version) ===");
        let sizes = [1_000, 10_000, 100_000];
        let repeat_count = 5;
        for &n in &sizes {
            println!(
                "-----------All Test Repeat: {}, All Tree Num: {}-------------------",
                repeat_count, n
            );
            let mut insert_times = Vec::with_capacity(repeat_count);
            let mut get_times = Vec::with_capacity(repeat_count);
            let mut remove_times = Vec::with_capacity(repeat_count);
            for _ in 0..repeat_count {
                let mut tree = RBTree::<MyNode, MyNodeAdapter>::new();
                // 1. Insert Test
                let start = Instant::now();
                for i in 0..n {
                    let node = TinyArc::new(MyNode::new(i as i32, "bench"));
                    let cmp = |a: &MyNode, b: &MyNode| a.key.cmp(&b.key);
                    black_box(tree.insert(node, cmp));
                }
                insert_times.push(start.elapsed());
                // 2. Get Test (key=20)
                let target_key = 20;
                let search_cmp = |k: &i32, n: &MyNode| k.cmp(&n.key);
                let start = Instant::now();
                black_box(tree.search(&target_key, search_cmp));
                get_times.push(start.elapsed());
                // 3. Remove Test (key=20)
                let start = Instant::now();
                black_box(tree.remove(&target_key, search_cmp));
                remove_times.push(start.elapsed());
            }
            print_stats("Insert Test", &insert_times, true);
            print_stats("Get data by key=20", &get_times, false);
            print_stats("Remove data by key=20", &remove_times, false);
            println!("-----------End Tree Test----------------------------------------------\n");
        }
    }
    fn print_stats(label: &str, times: &[Duration], use_micros: bool) {
        let max = times.iter().max().unwrap();
        let min = times.iter().min().unwrap();
        let sum: Duration = times.iter().sum();
        let avg = sum / times.len() as u32;
        if use_micros {
            println!(
                "{:<22} Max Cost: {}us, Min Cost: {}us, Aver Cost: {}us",
                format!("{},", label),
                max.as_micros(),
                min.as_micros(),
                avg.as_micros()
            );
        } else {
            println!(
                "{:<22} Max Cost: {}ns, Min Cost: {}ns, Aver Cost: {}ns",
                format!("{},", label),
                max.as_nanos(),
                min.as_nanos(),
                avg.as_nanos()
            );
        }
    }
    #[derive(Debug)]
    #[repr(C)]
    struct NoSentinelNode {
        key: i32,
        link1: RBLink,
        link2: RBLink,
    }
    impl NoSentinelNode {
        fn new(key: i32) -> Self {
            Self {
                key,
                link1: RBLink::new(),
                link2: RBLink::new(),
            }
        }
    }
    #[derive(Clone, Copy)]
    struct NoSentinelAdapter1;
    impl Adapter<NoSentinelNode> for NoSentinelAdapter1 {
        fn offset() -> usize {
            let dummy = std::mem::MaybeUninit::<NoSentinelNode>::uninit();
            unsafe {
                (std::ptr::addr_of!((*dummy.as_ptr()).link1) as usize) - (dummy.as_ptr() as usize)
            }
        }
    }
    #[derive(Clone, Copy)]
    struct NoSentinelAdapter2;
    impl Adapter<NoSentinelNode> for NoSentinelAdapter2 {
        fn offset() -> usize {
            let dummy = std::mem::MaybeUninit::<NoSentinelNode>::uninit();
            unsafe {
                (std::ptr::addr_of!((*dummy.as_ptr()).link2) as usize) - (dummy.as_ptr() as usize)
            }
        }
    }

    #[bench]
    fn bench_insert_and_detach_rbtree(b: &mut Bencher) {
        let n = 1 << 12;
        let cmp = |a: &NoSentinelNode, b: &NoSentinelNode| a.key.cmp(&b.key);
        let search_cmp = |k: &i32, n: &NoSentinelNode| k.cmp(&n.key);
        b.iter(|| {
            let mut tree1 = RBTree::<NoSentinelNode, NoSentinelAdapter1>::new();
            let mut tree2 = RBTree::<NoSentinelNode, NoSentinelAdapter2>::new();
            let mut nodes = Vec::with_capacity(n);

            for i in 0..n {
                let node = TinyArc::new(NoSentinelNode::new(i as i32));
                nodes.push(node.clone());

                tree1.insert(node.clone(), cmp);
                tree2.insert(node, cmp);
            }

            for node in &nodes {
                black_box(tree1.remove(&node.key, search_cmp));
                black_box(tree2.remove(&node.key, search_cmp));
            }
        });
    }

    #[bench]
    fn bench_insert_and_detach_btree_std(b: &mut Bencher) {
        use std::collections::BTreeMap;
        let n = 1 << 12;
        b.iter(|| {
            let mut map1 = BTreeMap::new();
            let mut map2 = BTreeMap::new();
            for i in 0..n {
                map1.insert(i, i);
                map2.insert(i, i);
            }
            for i in 0..n {
                black_box(map1.remove(&i));
                black_box(map2.remove(&i));
            }
        });
    }
}
