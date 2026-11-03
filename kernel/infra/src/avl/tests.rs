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

use super::*;
use std::{cell::Cell, collections::BTreeSet};

struct Node {
    key: usize,
    primary: AvlLink<Node>,
    secondary: AvlLink<Node>,
}

impl Node {
    fn new(key: usize) -> Self {
        Self {
            key,
            primary: AvlLink::new(),
            secondary: AvlLink::new(),
        }
    }
}

crate::impl_simple_intrusive_adapter!(Primary, Node, primary);
crate::impl_simple_intrusive_adapter!(Secondary, Node, secondary);
type Tree = AvlTree<Node, Primary>;

fn verify(tree: &Tree, expected: &BTreeSet<usize>) {
    unsafe fn walk(
        node: Option<NonNull<Node>>,
        lower: Option<usize>,
        upper: Option<usize>,
    ) -> usize {
        let Some(node) = node else { return 0 };
        let key = node.as_ref().key;
        assert!(lower.is_none_or(|lower| lower < key));
        assert!(upper.is_none_or(|upper| key < upper));
        let links = Tree::links(node).read();
        let left = walk(links.left, lower, Some(key));
        let right = walk(links.right, Some(key), upper);
        assert!(left.abs_diff(right) <= 1, "unbalanced node {key}");
        assert_eq!(links.height as usize, 1 + left.max(right));
        links.height as usize
    }
    unsafe { walk(tree.root, None, None) };
    let mut ordered = Vec::new();
    let result: ControlFlow<()> = tree.try_for_each(|node| {
        ordered.push(node.key);
        ControlFlow::Continue(())
    });
    assert_eq!(result, ControlFlow::Continue(()));
    assert_eq!(ordered, expected.iter().copied().collect::<Vec<_>>());
    assert_eq!(tree.is_empty(), expected.is_empty());
    for key in expected {
        assert_eq!(
            unsafe { tree.find(|node| key.cmp(&node.key)).unwrap().as_ref().key },
            *key
        );
    }
}

#[test]
fn all_rotation_shapes_keep_order_and_balance() {
    for order in [[3, 2, 1], [1, 2, 3], [3, 1, 2], [1, 3, 2]] {
        let nodes = order.map(Node::new);
        let mut tree = Tree::new();
        let mut expected = BTreeSet::new();
        for node in &nodes {
            unsafe {
                tree.insert(NonNull::from(node), |a, b| a.key.cmp(&b.key))
                    .unwrap()
            };
            expected.insert(node.key);
            verify(&tree, &expected);
        }
        assert_eq!(unsafe { tree.root.unwrap().as_ref().key }, 2);
        for key in [2, 1, 3] {
            let node = tree.remove(|node| key.cmp(&node.key)).unwrap();
            assert!(!unsafe { node.as_ref().primary.is_linked() });
            expected.remove(&key);
            verify(&tree, &expected);
        }
    }
}

#[test]
fn mixed_insertions_and_deletions_preserve_all_invariants() {
    const N: usize = 31;
    let nodes: Vec<_> = (0..N).map(Node::new).collect();
    for (insert_step, remove_step) in [(1, 1), (30, 30), (7, 13)] {
        let mut tree = Tree::new();
        let mut expected = BTreeSet::new();
        assert_eq!(tree.remove(|node| 0.cmp(&node.key)), None);
        for i in 0..N {
            let node = &nodes[(i * insert_step) % N];
            unsafe {
                tree.insert(NonNull::from(node), |a, b| a.key.cmp(&b.key))
                    .unwrap()
            };
            expected.insert(node.key);
            verify(&tree, &expected);
        }
        assert_eq!(tree.remove(|node| N.cmp(&node.key)), None);
        for i in 0..N {
            let node = &nodes[(i * remove_step) % N];
            assert_eq!(
                tree.remove(|other| node.key.cmp(&other.key)),
                Some(NonNull::from(node))
            );
            expected.remove(&node.key);
            verify(&tree, &expected);
        }
    }
}

#[test]
fn duplicate_keys_and_linked_nodes_leave_the_tree_unchanged() {
    let nodes = [Node::new(7), Node::new(7)];
    let mut tree = Tree::new();
    let mut other = Tree::new();
    let first = NonNull::from(&nodes[0]);
    let duplicate = NonNull::from(&nodes[1]);
    unsafe {
        tree.insert(first, |a, b| a.key.cmp(&b.key)).unwrap();
        assert_eq!(
            tree.insert(first, |a, b| a.key.cmp(&b.key)),
            Err(InsertError::AlreadyLinked)
        );
        assert_eq!(
            other.insert(first, |a, b| a.key.cmp(&b.key)),
            Err(InsertError::AlreadyLinked)
        );
        assert_eq!(
            tree.insert(duplicate, |a, b| a.key.cmp(&b.key)),
            Err(InsertError::DuplicateKey)
        );
        assert!(!nodes[1].primary.is_linked());
    }
    assert_eq!(tree.find(|node| 7.cmp(&node.key)), Some(first));
    assert!(other.is_empty());
    assert_eq!(tree.remove(|node| 7.cmp(&node.key)), Some(first));
    unsafe { other.insert(first, |a, b| a.key.cmp(&b.key)).unwrap() };
    assert_eq!(other.remove(|node| 7.cmp(&node.key)), Some(first));
}

#[test]
fn two_adapters_allow_independent_orderings_and_tree_moves() {
    let nodes = [Node::new(1), Node::new(2), Node::new(3)];
    let mut ascending = Tree::new();
    let mut descending = AvlTree::<Node, Secondary>::new();
    for node in &nodes {
        unsafe {
            ascending
                .insert(NonNull::from(node), |a, b| a.key.cmp(&b.key))
                .unwrap();
            descending
                .insert(NonNull::from(node), |a, b| b.key.cmp(&a.key))
                .unwrap();
        }
    }
    let mut moved = Box::new(ascending);
    let mut visited = Vec::new();
    let result = descending.try_for_each(|node| {
        visited.push(node.key);
        if node.key == 2 {
            ControlFlow::Break(node.key)
        } else {
            ControlFlow::Continue(())
        }
    });
    assert_eq!(result, ControlFlow::Break(2));
    assert_eq!(visited, [3, 2]);
    for node in &nodes {
        assert_eq!(
            moved.remove(|other| node.key.cmp(&other.key)),
            Some(NonNull::from(node))
        );
        assert_eq!(
            descending.find(|other| other.key.cmp(&node.key)),
            Some(NonNull::from(node))
        );
        assert!(!unsafe { node.primary.is_linked() });
        assert!(unsafe { node.secondary.is_linked() });
    }
    for node in &nodes {
        assert_eq!(
            descending.remove(|other| other.key.cmp(&node.key)),
            Some(NonNull::from(node))
        );
    }
}

#[test]
fn sorted_input_keeps_comparison_counts_logarithmic() {
    const N: usize = 127;
    let nodes: Vec<_> = (0..N).map(Node::new).collect();
    let mut tree = Tree::new();
    let limit = 2 * (usize::BITS - N.leading_zeros()) as usize;
    for node in &nodes {
        let comparisons = Cell::new(0);
        unsafe {
            tree.insert(NonNull::from(node), |a, b| {
                comparisons.set(comparisons.get() + 1);
                a.key.cmp(&b.key)
            })
            .unwrap();
        }
        assert!(comparisons.get() <= limit);
    }
    for node in &nodes {
        let comparisons = Cell::new(0);
        assert_eq!(
            tree.find(|other| {
                comparisons.set(comparisons.get() + 1);
                node.key.cmp(&other.key)
            }),
            Some(NonNull::from(node))
        );
        assert!(comparisons.get() <= limit);
    }
    for node in nodes.iter().rev() {
        let comparisons = Cell::new(0);
        assert_eq!(
            tree.remove(|other| {
                comparisons.set(comparisons.get() + 1);
                node.key.cmp(&other.key)
            }),
            Some(NonNull::from(node))
        );
        assert!(comparisons.get() <= limit);
    }
}
