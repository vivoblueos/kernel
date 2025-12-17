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

#[warn(unused_imports)]
use core::{marker::PhantomData, ops::Drop};
use std::{boxed::Box, cmp::Ordering, fmt::Debug, ptr};

#[derive(Debug, Clone, Copy, PartialEq)]
#[warn(unused_imports)]
pub enum Color {
    Red,
    Black,
}

#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(C)]
pub struct RBLink {
    color: Color,
    parent: *mut RBLink,
    right: *mut RBLink,
    left: *mut RBLink,
}

impl RBLink {
    pub fn new() -> Self {
        Self {
            color: Color::Red,
            parent: ptr::null_mut(),
            right: ptr::null_mut(),
            left: ptr::null_mut(),
        }
    }

    #[inline]
    pub fn is_red(&self) -> bool {
        self.color == Color::Red
    }
}

pub struct RBTree<T, A: Adapter<T>> {
    root: *mut RBLink,
    size: usize,
    //Set sentry to judge null and double-black situation to make ptr opreation easy.
    nil: *mut RBLink,
    _marker: PhantomData<(T, A)>,
}

impl<T, A: Adapter<T>> RBTree<T, A> {
    pub fn new() -> Self {
        unsafe {
            // Color of sentry must be black so that black height can be ensured.
            let nil_link = Box::new(RBLink {
                color: Color::Black,
                parent: ptr::null_mut(),
                right: ptr::null_mut(),
                left: ptr::null_mut(),
            });

            let nil = Box::into_raw(nil_link);
            (*nil).left = nil;
            (*nil).right = nil;
            (*nil).parent = nil;

            Self {
                root: nil,
                size: 0,
                nil,
                _marker: PhantomData,
            }
        }
    }

    unsafe fn get_link(&self, object: *mut T) -> *mut RBLink {
        unsafe {
            if object.is_null() {
                return self.nil;
            }

            (object as *mut u8).add(A::offset()) as *mut RBLink
        }
    }

    pub unsafe fn get_obj(&self, link: *mut RBLink) -> *mut T {
        unsafe {
            if link == self.nil || link.is_null() {
                return ptr::null_mut();
            }

            (link as *mut u8).sub(A::offset()) as *mut T
        }
    }

    pub fn search<K, F>(&self, key: &K, compare: F) -> Option<&T>
    where
        F: Fn(&K, &T) -> Ordering,
    {
        unsafe {
            let mut current = self.root;
            while current != self.nil {
                let current_obj = self.get_obj(current);
                match compare(key, &*current_obj) {
                    Ordering::Equal => return Some(&*current_obj),
                    Ordering::Less => current = (*current).left,
                    Ordering::Greater => current = (*current).right,
                }
            }
        }
        None
    }

    pub fn insert<F>(&mut self, object: *mut T, compare: F)
    where
        F: Fn(&T, &T) -> Ordering,
    {
        unsafe {
            // New node two children point to sentry.
            let new_link = self.get_link(object);
            (*new_link).left = self.nil;
            (*new_link).right = self.nil;
            (*new_link).color = Color::Red;
            let mut y = self.nil;
            let mut x = self.root;

            while x != self.nil {
                y = x;
                let x_obj = self.get_obj(x);

                match compare(&*object, &*x_obj) {
                    Ordering::Less => x = (*x).left,
                    Ordering::Greater => x = (*x).right,
                    Ordering::Equal => return,
                }
            }

            (*new_link).parent = y;

            if y == self.nil {
                self.root = new_link;
            } else {
                let y_obj = self.get_obj(y);
                match compare(&*object, &*y_obj) {
                    Ordering::Less => (*y).left = new_link,
                    _ => (*y).right = new_link,
                }
            }

            self.size += 1;
            self.fix_after_insertion(new_link);
        }
    }

    pub fn fix_after_insertion(&mut self, mut z: *mut RBLink) {
        unsafe {
            while z != self.root && (*((*z).parent)).is_red() {
                let parent = (*z).parent;
                let grandparent = (*parent).parent;
                let is_parent_left = (*grandparent).left == parent;
                let uncle = if is_parent_left {
                    (*grandparent).right
                } else {
                    (*grandparent).left
                };

                // Situation 2. Uncle is red.
                if uncle != self.nil && (*uncle).is_red() {
                    (*parent).color = Color::Black;
                    (*uncle).color = Color::Black;
                    (*grandparent).color = Color::Red;
                    z = grandparent;
                    continue;
                }

                let is_link_left = (*parent).left == z;

                // Situation 2, direction is differnt with parent.
                if is_parent_left ^ is_link_left {
                    if is_parent_left {
                        self.rotate_left(parent);
                    } else {
                        self.rotate_right(parent);
                    }

                    z = parent;
                    continue;
                }

                // Situation 2, direction is same to parent.
                (*parent).color = Color::Black;
                (*grandparent).color = Color::Red;

                if is_parent_left {
                    self.rotate_right(grandparent);
                } else {
                    self.rotate_left(grandparent);
                }

                break;
            }

            // Sometime we changed color of root.
            (*self.root).color = Color::Black;
        }
    }

    pub fn rotate_left(&mut self, x: *mut RBLink) {
        unsafe {
            let right = (*x).right;
            (*x).right = (*right).left;

            if (*right).left != self.nil {
                (*(*right).left).parent = x;
            }

            (*right).parent = (*x).parent;
            let parent = (*x).parent;

            if x == self.root {
                self.root = right;
            } else if x == (*parent).left {
                (*parent).left = right;
            } else {
                (*parent).right = right;
            }

            (*right).left = x;
            (*x).parent = right;
        }
    }

    pub fn rotate_right(&mut self, x: *mut RBLink) {
        unsafe {
            let left = (*x).left;
            (*x).left = (*left).right;

            if (*left).right != self.nil {
                let left_right = (*left).right;
                (*left_right).parent = x;
            }

            (*left).parent = (*x).parent;
            let parent = (*x).parent;

            if x == self.root {
                self.root = left;
            } else if x == (*parent).right {
                (*parent).right = left;
            } else {
                (*parent).left = left;
            }

            (*left).right = x;
            (*x).parent = left;
        }
    }

    pub fn minimum(&self, mut node: *mut RBLink) -> *mut RBLink {
        unsafe {
            while node != self.nil {
                if (*node).left == self.nil {
                    break;
                }
                node = (*node).left;
            }
        }
        node
    }

    pub fn maximum(&self, mut node: *mut RBLink) -> *mut RBLink {
        unsafe {
            while node != self.nil {
                if (*node).right == self.nil {
                    break;
                }
                node = (*node).right;
            }
            node
        }
    }

    pub fn delete(&mut self, object: *mut T) {
        unsafe {
            let node = self.get_link(object);
            if node == self.nil || node.is_null() {
                return;
            }

            self.delete_node(node);
            self.size -= 1;
        }
    }

    pub unsafe fn delete_node(&mut self, z: *mut RBLink) {
        unsafe {
            let mut y = z;
            let mut y_original_color = (*y).color;
            let x;
            let x_parent;

            // Situation 1: Only a child
            if (*z).left == self.nil {
                x = (*z).right;
                self.transplant(z, (*z).right);
                x_parent = (*z).parent;
            } else if (*z).right == self.nil {
                x = (*z).left;
                self.transplant(z, (*z).left);
                x_parent = (*z).parent;
            } else {
                // Situation 2: left and right both exists
                y = self.minimum((*z).right);
                y_original_color = (*y).color;
                x = (*y).right;

                if (*y).parent == z {
                    //(*x).parent = y;
                    x_parent = y;
                } else {
                    x_parent = (*y).parent;

                    self.transplant(y, x);
                    (*y).right = (*z).right;
                    let node_right = (*y).right;
                    (*node_right).parent = y;
                }

                self.transplant(z, y);
                (*y).left = (*z).left;
                (*(*y).left).parent = y;
                (*y).color = (*z).color;
            }

            // If delete a black node, black height changed. Fix it!!!
            if y_original_color == Color::Black {
                self.fix_after_deletion(x, x_parent);
            }

            //In case of overhang ref.
            (*z).left = ptr::null_mut();
            (*z).right = ptr::null_mut();
            (*z).parent = ptr::null_mut();
        }
    }

    pub unsafe fn transplant(&mut self, u: *mut RBLink, v: *mut RBLink) {
        unsafe {
            if (*u).parent == self.nil {
                self.root = v;
            } else if u == (*(*u).parent).left {
                (*(*u).parent).left = v;
            } else {
                (*(*u).parent).right = v;
            }
            if v != self.nil {
                (*v).parent = (*u).parent;
            }
        }
    }

    pub unsafe fn fix_after_deletion(&mut self, mut x: *mut RBLink, mut parent: *mut RBLink) {
        unsafe {
            //w is sibling of x.
            while x != self.root && !(*x).is_red() {
                if x != self.nil {
                    parent = (*x).parent;
                }

                let is_x_left = x == (*parent).left;
                let mut w = if is_x_left {
                    (*parent).right
                } else {
                    (*parent).left
                };

                // Situation 1: w is red.
                if (*w).is_red() {
                    (*w).color = Color::Black;
                    (*parent).color = Color::Red;

                    if is_x_left {
                        self.rotate_left(parent);
                        w = (*parent).right;
                    } else {
                        self.rotate_right(parent);
                        w = (*parent).left;
                    }
                }

                // situation 2: x and w are black.
                if !(*(*w).left).is_red() && !(*(*w).right).is_red() {
                    (*w).color = Color::Red;
                    x = parent;
                } else {
                    if is_x_left {
                        // Situation 3：sibling is black with red left and black right.
                        if !(*(*w).right).is_red() {
                            (*(*w).left).color = Color::Black;
                            (*w).color = Color::Red;
                            self.rotate_right(w);
                            w = (*parent).right;
                        }

                        // Situation 4：sibling is black with red right.
                        (*w).color = (*parent).color;
                        (*parent).color = Color::Black;
                        (*(*w).right).color = Color::Black;
                        self.rotate_left(parent);
                        x = self.root;
                    } else {
                        // Situation 5：sibling is black with red right and black left.
                        if !(*(*w).left).is_red() {
                            (*(*w).right).color = Color::Black;
                            (*w).color = Color::Red;
                            self.rotate_left(w);
                            w = (*parent).left;
                        }

                        // Situation 6：sibling is black with red left.
                        (*w).color = (*parent).color;
                        (*parent).color = Color::Black;
                        (*(*w).left).color = Color::Black;
                        self.rotate_right(parent);
                        x = self.root;
                    }
                }
            }

            (*x).color = Color::Black;
        }
    }

    pub fn print_structure(&self)
    where
        T: std::fmt::Debug,
    {
        unsafe {
            self.print_node(self.root, 0);
        }
    }

    unsafe fn print_node(&self, node: *mut RBLink, depth: usize)
    where
        T: std::fmt::Debug,
    {
        unsafe {
            if node == self.nil || node.is_null() {
                return;
            }
            self.print_node((*node).right, depth + 1);
            let indent = "    ".repeat(depth);
            let obj = self.get_obj(node);
            let color = if (*node).is_red() { "RED" } else { "BLK" };
            println!("{}Node ({}) -> {:?}", indent, color, *obj);
            self.print_node((*node).left, depth + 1);
        }
    }

    pub fn iter(&self) -> RBIterator<'_, T, A> {
        RBIterator::new(self)
    }
}

pub struct RBIterator<'a, T, A: Adapter<T>> {
    tree: &'a RBTree<T, A>,
    stack: Vec<*mut RBLink>,
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

    pub unsafe fn push_left(&mut self, mut node: *mut RBLink) {
        unsafe {
            while node != self.tree.nil {
                self.stack.push(node);
                node = (*node).left;
            }
        }
    }
}

impl<'a, T, A: Adapter<T>> Iterator for RBIterator<'a, T, A> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            let node = self.stack.pop()?;
            let right = (*node).right;
            if right != self.tree.nil {
                self.push_left(right);
            }
            let obj_ptr = self.tree.get_obj(node);
            Some(&*obj_ptr)
        }
    }
}

impl<T, A: Adapter<T>> Drop for RBTree<T, A> {
    fn drop(&mut self) {
        unsafe {
            drop(Box::from_raw(self.nil));
        }
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    use std::{
        boxed::Box,
        string::{String, ToString},
        vec::Vec,
    };

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
        if tree.root == tree.nil {
            return;
        }

        unsafe {
            assert!((*tree.root).color == Color::Black, "Root must be black");
            check_node_properties(tree, tree.root, tree.nil);
        }
    }

    unsafe fn check_node_properties(
        tree: &RBTree<MyNode, MyNodeAdapter>,
        node: *mut RBLink,
        nil: *mut RBLink,
    ) -> usize {
        unsafe {
            if node == nil {
                return 1;
            }

            let left = (*node).left;
            let right = (*node).right;

            if (*node).is_red() {
                assert!(!(*left).is_red(), "Red node has red left child");
                assert!(!(*right).is_red(), "Red node has red right child");
            }

            let left_bh = check_node_properties(tree, left, nil);
            let right_bh = check_node_properties(tree, right, nil);

            assert_eq!(left_bh, right_bh, "Black height mismatch at node");

            if (*node).color == Color::Black {
                left_bh + 1
            } else {
                left_bh
            }
        }
    }

    #[test]
    fn test_insert_and_search() {
        let mut tree = RBTree::<MyNode, MyNodeAdapter>::new();
        let cmp = |a: &MyNode, b: &MyNode| a.key.cmp(&b.key);
        let search_cmp = |k: &i32, n: &MyNode| k.cmp(&n.key);
        let n1 = Box::into_raw(Box::new(MyNode::new(10, "Ten")));
        let n2 = Box::into_raw(Box::new(MyNode::new(5, "Five")));
        let n3 = Box::into_raw(Box::new(MyNode::new(20, "Twenty")));

        unsafe {
            tree.insert(n1, cmp);
            tree.insert(n2, cmp);
            tree.insert(n3, cmp);

            check_rb_properties(&tree);
        }

        assert_eq!(tree.size, 3);
        eprintln!("============================");
        tree.print_structure();
        let res = tree.search(&10, search_cmp);
        assert!(res.is_some());
        assert_eq!(res.unwrap().value, "Ten");
        let res = tree.search(&99, search_cmp);
        assert!(res.is_none());

        unsafe {
            drop(Box::from_raw(n1));
            drop(Box::from_raw(n2));
            drop(Box::from_raw(n3));
        }
    }
    #[test]
    fn test_delete_complex() {
        let mut tree = RBTree::<MyNode, MyNodeAdapter>::new();
        let cmp = |a: &MyNode, b: &MyNode| a.key.cmp(&b.key);
        let mut nodes = Vec::new();

        for i in 0..20 {
            let node = Box::into_raw(Box::new(MyNode::new(i, "Val")));
            nodes.push(node);
            tree.insert(node, cmp);
        }

        eprintln!("=============before delete===============");
        tree.print_structure();

        unsafe {
            check_rb_properties(&tree);
        }
        assert_eq!(tree.size, 20);

        unsafe {
            for i in (0..20).step_by(2) {
                let node_ptr = nodes[i as usize];
                tree.delete(node_ptr);
                check_rb_properties(&tree);
                drop(Box::from_raw(node_ptr));
            }
        }

        eprintln!("=============after delete================");
        tree.print_structure();
        assert_eq!(tree.size, 10);

        unsafe {
            for i in (1..20).step_by(2) {
                let node_ptr = nodes[i as usize];
                drop(Box::from_raw(node_ptr));
            }
        }
    }
    #[test]
    fn test_iterator() {
        let mut tree = RBTree::<MyNode, MyNodeAdapter>::new();
        let cmp = |a: &MyNode, b: &MyNode| a.key.cmp(&b.key);
        let ptrs = [
            Box::into_raw(Box::new(MyNode::new(3, "C"))),
            Box::into_raw(Box::new(MyNode::new(1, "A"))),
            Box::into_raw(Box::new(MyNode::new(2, "B"))),
            Box::into_raw(Box::new(MyNode::new(4, "D"))),
        ];

        for p in &ptrs {
            tree.insert(*p, cmp);
        }

        tree.print_structure();
        let mut iter = tree.iter();
        assert_eq!(iter.next().unwrap().key, 1);
        assert_eq!(iter.next().unwrap().key, 2);
        assert_eq!(iter.next().unwrap().key, 3);
        assert_eq!(iter.next().unwrap().key, 4);
        assert!(iter.next().is_none());
        unsafe {
            for p in ptrs {
                drop(Box::from_raw(p));
            }
        }
    }

    #[test]
    fn test_sequential_insert_stress() {
        let mut tree = RBTree::<MyNode, MyNodeAdapter>::new();
        let cmp = |a: &MyNode, b: &MyNode| a.key.cmp(&b.key);
        let count = 2000;
        let mut nodes = Vec::new();

        for i in 0..count {
            let val_str = format!("Val-{}", i);
            let node = Box::into_raw(Box::new(MyNode::new(i, &val_str)));
            nodes.push(node);
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

        unsafe {
            for node in nodes {
                drop(Box::from_raw(node));
            }
        }
    }

    #[test]
    fn test_delete_root_scenarios() {
        let mut tree = RBTree::<MyNode, MyNodeAdapter>::new();
        let cmp = |a: &MyNode, b: &MyNode| a.key.cmp(&b.key);
        let n1 = Box::into_raw(Box::new(MyNode::new(10, "Root")));

        unsafe {
            tree.insert(n1, cmp);
            tree.delete(n1);
            assert_eq!(tree.size, 0);
            assert_eq!(tree.root, tree.nil);
            drop(Box::from_raw(n1));
        }

        let n1 = Box::into_raw(Box::new(MyNode::new(10, "Root")));
        let n2 = Box::into_raw(Box::new(MyNode::new(5, "Left")));

        unsafe {
            tree.insert(n1, cmp);
            tree.insert(n2, cmp);
            tree.delete(n1);
            assert_eq!(tree.size, 1);
            assert_eq!(tree.root, tree.get_link(n2));
            assert!((*tree.root).color == Color::Black);
            tree.delete(n2);
            drop(Box::from_raw(n1));
            drop(Box::from_raw(n2));
        }

        let n1 = Box::into_raw(Box::new(MyNode::new(10, "Root")));
        let n2 = Box::into_raw(Box::new(MyNode::new(15, "Right")));

        unsafe {
            tree.insert(n1, cmp);
            tree.insert(n2, cmp);
            tree.delete(n1);
            assert_eq!(tree.size, 1);
            assert_eq!(tree.root, tree.get_link(n2));
            assert!((*tree.root).color == Color::Black);
            drop(Box::from_raw(n1));
            drop(Box::from_raw(n2));
        }
    }

    #[test]
    fn test_clrs_13_4_3() {
        let mut tree = RBTree::<MyNode, MyNodeAdapter>::new();
        let cmp = |a: &MyNode, b: &MyNode| a.key.cmp(&b.key);
        let n1 = Box::into_raw(Box::new(MyNode::new(41, "Forty_one")));
        let n2 = Box::into_raw(Box::new(MyNode::new(38, "Thirty_eight")));
        let n3 = Box::into_raw(Box::new(MyNode::new(31, "Thirty_one")));
        let n4 = Box::into_raw(Box::new(MyNode::new(12, "Twelve")));
        let n5 = Box::into_raw(Box::new(MyNode::new(19, "Nineteen")));
        let n6 = Box::into_raw(Box::new(MyNode::new(8, "Eight")));

        unsafe {
            eprintln!("=========insert node========");
            tree.insert(n1, cmp);
            tree.insert(n2, cmp);
            tree.insert(n3, cmp);
            tree.insert(n4, cmp);
            tree.insert(n5, cmp);
            tree.insert(n6, cmp);
            tree.print_structure();

            eprintln!("========delete node=========");
            tree.delete(n6);
            eprintln!("========delete node6=========");
            tree.print_structure();

            tree.delete(n4);
            eprintln!("========delete node4=========");
            tree.print_structure();

            tree.delete(n5);
            eprintln!("========delete node5=========");
            tree.print_structure();

            tree.delete(n3);
            eprintln!("========delete node3=========");
            tree.print_structure();

            tree.delete(n2);
            eprintln!("========delete node2=========");
            tree.print_structure();

            tree.delete(n1);
            eprintln!("========delete node1=========");
            tree.print_structure();

            drop(Box::from_raw(n1));
            drop(Box::from_raw(n2));
            drop(Box::from_raw(n3));
            drop(Box::from_raw(n4));
            drop(Box::from_raw(n5));
            drop(Box::from_raw(n6));
        }
    }
}

#[cfg(test)]
mod benches {
    extern crate test;
    use super::*;
    use std::{boxed::Box, collections::BTreeMap, vec::Vec};
    use test::Bencher;

    #[derive(Debug)]
    struct BenchNode {
        key: i32,
        link1: RBLink,
        link2: RBLink,
    }
    impl BenchNode {
        fn new(key: i32) -> Self {
            Self {
                key,
                link1: RBLink::new(),
                link2: RBLink::new(),
            }
        }
    }

    #[derive(Clone, Copy)]
    struct Adapter1;
    impl Adapter<BenchNode> for Adapter1 {
        fn offset() -> usize {
            let dummy = std::mem::MaybeUninit::<BenchNode>::uninit();
            let dummy_ptr = dummy.as_ptr();
            unsafe {
                let member_ptr = std::ptr::addr_of!((*dummy_ptr).link1);
                (member_ptr as usize) - (dummy_ptr as usize)
            }
        }
    }

    #[derive(Clone, Copy)]
    struct Adapter2;
    impl Adapter<BenchNode> for Adapter2 {
        fn offset() -> usize {
            let dummy = std::mem::MaybeUninit::<BenchNode>::uninit();
            let dummy_ptr = dummy.as_ptr();
            unsafe {
                let member_ptr = std::ptr::addr_of!((*dummy_ptr).link2);
                (member_ptr as usize) - (dummy_ptr as usize)
            }
        }
    }

    #[bench]
    fn bench_rbtree_insert_and_delete_2_trees(b: &mut Bencher) {
        // data scale：2^12 = 4096.
        let n = 1 << 12;

        let cmp = |a: &BenchNode, b: &BenchNode| a.key.cmp(&b.key);
        b.iter(|| {
            let mut tree1 = RBTree::<BenchNode, Adapter1>::new();
            let mut tree2 = RBTree::<BenchNode, Adapter2>::new();
            let mut nodes = Vec::with_capacity(n);

            for i in 0..n {
                let node = Box::into_raw(Box::new(BenchNode::new(i as i32)));
                nodes.push(node);
                tree1.insert(node, cmp);
                tree2.insert(node, cmp);
            }

            for node in &nodes {
                tree1.delete(*node);
                tree2.delete(*node);
            }
            // In real Operation, arc do it propably, but we dropping node by ourselves.
            for node in nodes {
                unsafe {
                    drop(Box::from_raw(node));
                }
            }
        });
    }

    //Comparation: std::btree
    #[bench]
    fn bench_std_btree_insert_and_delete_2_trees(b: &mut Bencher) {
        let n = 1 << 12;
        b.iter(|| {
            let mut map1 = BTreeMap::new();
            let mut map2 = BTreeMap::new();

            for i in 0..n {
                map1.insert(i, i);
                map2.insert(i, i);
            }

            for i in 0..n {
                map1.remove(&i);
                map2.remove(&i);
            }
        });
    }
}
