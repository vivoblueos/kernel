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

//! Allocation-free intrusive AVL trees over externally owned, stable nodes.
//!
//! Embed one [`AvlLink`] per index and select it with an [`Adapter`]. The tree
//! neither allocates nor frees nodes. Insertion, removal and ordered lookup are
//! O(log N); in-order traversal is O(N), with O(log N) recursive stack space.
//! Links are mutated through their own `UnsafeCell`, never through `&mut T`, so
//! separate links in one object can be managed under independent external locks.

use crate::intrusive::Adapter;
use core::{cell::UnsafeCell, cmp::Ordering, marker::PhantomData, ops::ControlFlow, ptr::NonNull};

struct Links<T> {
    left: Option<NonNull<T>>,
    right: Option<NonNull<T>>,
    height: u8,
}

impl<T> Links<T> {
    const fn new() -> Self {
        Self {
            left: None,
            right: None,
            height: 0,
        }
    }
}

/// An embedded link for one AVL index. A node may contain several such links.
pub struct AvlLink<T> {
    links: UnsafeCell<Links<T>>,
}

impl<T> AvlLink<T> {
    pub const fn new() -> Self {
        Self {
            links: UnsafeCell::new(Links::new()),
        }
    }

    /// Whether this link belongs to a tree, including a single-node tree.
    ///
    /// # Safety
    /// The caller must exclude concurrent modifications of this link.
    pub unsafe fn is_linked(&self) -> bool {
        unsafe { (*self.links.get()).height != 0 }
    }
}

impl<T> Default for AvlLink<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InsertError {
    AlreadyLinked,
    DuplicateKey,
}

/// A non-owning AVL index whose adapter selects an embedded `AvlLink<T>`.
///
/// Dropping the tree does not detach or free nodes. Remove nodes before reusing
/// their links. Moving a tree does not move its nodes or invalidate its links.
pub struct AvlTree<T, A: Adapter<T>> {
    root: Option<NonNull<T>>,
    _adapter: PhantomData<A>,
}

// Sending or sharing the index also exposes the externally retained nodes.
unsafe impl<T: Send + Sync, A: Adapter<T> + Send> Send for AvlTree<T, A> {}
unsafe impl<T: Sync, A: Adapter<T> + Sync> Sync for AvlTree<T, A> {}

impl<T, A: Adapter<T>> Default for AvlTree<T, A> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T, A: Adapter<T>> AvlTree<T, A> {
    pub const fn new() -> Self {
        Self {
            root: None,
            _adapter: PhantomData,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.root.is_none()
    }

    unsafe fn links(node: NonNull<T>) -> *mut Links<T> {
        let link = node
            .as_ptr()
            .cast::<u8>()
            .add(A::offset())
            .cast::<AvlLink<T>>();
        (*link).links.get()
    }

    unsafe fn height(node: Option<NonNull<T>>) -> i16 {
        node.map_or(0, |node| (*Self::links(node)).height as i16)
    }

    unsafe fn update(node: NonNull<T>) {
        let links = Self::links(node);
        (*links).height = (1 + Self::height((*links).left).max(Self::height((*links).right))) as u8;
    }

    unsafe fn rotate_left(node: NonNull<T>) -> NonNull<T> {
        let top = (*Self::links(node)).right.unwrap();
        (*Self::links(node)).right = (*Self::links(top)).left;
        (*Self::links(top)).left = Some(node);
        Self::update(node);
        Self::update(top);
        top
    }

    unsafe fn rotate_right(node: NonNull<T>) -> NonNull<T> {
        let top = (*Self::links(node)).left.unwrap();
        (*Self::links(node)).left = (*Self::links(top)).right;
        (*Self::links(top)).right = Some(node);
        Self::update(node);
        Self::update(top);
        top
    }

    unsafe fn balance(node: NonNull<T>) -> NonNull<T> {
        Self::update(node);
        let links = Self::links(node);
        let balance = Self::height((*links).left) - Self::height((*links).right);
        if balance > 1 {
            let child = (*links).left.unwrap();
            let child_links = Self::links(child);
            if Self::height((*child_links).left) < Self::height((*child_links).right) {
                (*links).left = Some(Self::rotate_left(child));
            }
            return Self::rotate_right(node);
        }
        if balance < -1 {
            let child = (*links).right.unwrap();
            let child_links = Self::links(child);
            if Self::height((*child_links).right) < Self::height((*child_links).left) {
                (*links).right = Some(Self::rotate_right(child));
            }
            return Self::rotate_left(node);
        }
        node
    }

    /// Insert a node, rejecting a linked node or an equal key without mutation.
    ///
    /// # Safety
    /// `A::offset()` must select an initialized `AvlLink<T>` in every node. The
    /// caller must keep nodes alive at stable addresses until removal or the
    /// tree's last use, and serialize all access to this selected link, including
    /// access through other trees. Comparisons must define a consistent total
    /// order; ordering fields must stay immutable while linked. Shared node
    /// references must permit link mutation through `AvlLink`'s `UnsafeCell`.
    pub unsafe fn insert<F>(&mut self, node: NonNull<T>, compare: F) -> Result<(), InsertError>
    where
        F: Fn(&T, &T) -> Ordering,
    {
        unsafe fn add<T, A: Adapter<T>, F: Fn(&T, &T) -> Ordering>(
            root: Option<NonNull<T>>,
            node: NonNull<T>,
            compare: &F,
        ) -> Result<NonNull<T>, InsertError> {
            let Some(root) = root else {
                (*AvlTree::<T, A>::links(node)).height = 1;
                return Ok(node);
            };
            let links = AvlTree::<T, A>::links(root);
            match compare(node.as_ref(), root.as_ref()) {
                Ordering::Less => {
                    (*links).left = Some(add::<T, A, F>((*links).left, node, compare)?)
                }
                Ordering::Greater => {
                    (*links).right = Some(add::<T, A, F>((*links).right, node, compare)?)
                }
                Ordering::Equal => return Err(InsertError::DuplicateKey),
            }
            Ok(AvlTree::<T, A>::balance(root))
        }
        if (*Self::links(node)).height != 0 {
            return Err(InsertError::AlreadyLinked);
        }
        self.root = Some(add::<T, A, F>(self.root, node, &compare)?);
        Ok(())
    }

    /// Find a node in O(log N). `compare(node)` compares the sought key with
    /// that node's key, using the same ordering as insertion.
    pub fn find<F: Fn(&T) -> Ordering>(&self, compare: F) -> Option<NonNull<T>> {
        let mut next = self.root;
        while let Some(node) = next {
            unsafe {
                let links = Self::links(node);
                match compare(node.as_ref()) {
                    Ordering::Less => next = (*links).left,
                    Ordering::Greater => next = (*links).right,
                    Ordering::Equal => return Some(node),
                }
            }
        }
        None
    }

    /// Remove and detach a node in O(log N), using the same key comparison as
    /// `find`. The caller regains exclusive ownership of the selected link.
    pub fn remove<F: Fn(&T) -> Ordering>(&mut self, compare: F) -> Option<NonNull<T>> {
        unsafe fn minimum<T, A: Adapter<T>>(node: NonNull<T>) -> (Option<NonNull<T>>, NonNull<T>) {
            let links = AvlTree::<T, A>::links(node);
            if let Some(left) = (*links).left {
                let (left, found) = minimum::<T, A>(left);
                (*links).left = left;
                (Some(AvlTree::<T, A>::balance(node)), found)
            } else {
                ((*links).right, node)
            }
        }
        unsafe fn take<T, A: Adapter<T>, F: Fn(&T) -> Ordering>(
            root: Option<NonNull<T>>,
            compare: &F,
            found: &mut Option<NonNull<T>>,
        ) -> Option<NonNull<T>> {
            let root = root?;
            let links = AvlTree::<T, A>::links(root);
            match compare(root.as_ref()) {
                Ordering::Less => (*links).left = take::<T, A, F>((*links).left, compare, found),
                Ordering::Greater => {
                    (*links).right = take::<T, A, F>((*links).right, compare, found)
                }
                Ordering::Equal => {
                    *found = Some(root);
                    let (left, right) = ((*links).left, (*links).right);
                    links.write(Links::new());
                    return match (left, right) {
                        (None, right) => right,
                        (left, None) => left,
                        (left, Some(right)) => {
                            let (right, top) = minimum::<T, A>(right);
                            let top_links = AvlTree::<T, A>::links(top);
                            (*top_links).left = left;
                            (*top_links).right = right;
                            Some(AvlTree::<T, A>::balance(top))
                        }
                    };
                }
            }
            Some(AvlTree::<T, A>::balance(root))
        }
        let mut found = None;
        unsafe { self.root = take::<T, A, F>(self.root, &compare, &mut found) };
        found
    }

    /// Visit nodes in key order, stopping immediately on `ControlFlow::Break`.
    /// This traversal allocates no memory and uses O(log N) stack space.
    pub fn try_for_each<B, F: FnMut(&T) -> ControlFlow<B>>(&self, mut visit: F) -> ControlFlow<B> {
        unsafe fn walk<T, A: Adapter<T>, B, F: FnMut(&T) -> ControlFlow<B>>(
            node: Option<NonNull<T>>,
            visit: &mut F,
        ) -> ControlFlow<B> {
            if let Some(node) = node {
                let links = AvlTree::<T, A>::links(node);
                walk::<T, A, B, F>((*links).left, visit)?;
                visit(node.as_ref())?;
                walk::<T, A, B, F>((*links).right, visit)?;
            }
            ControlFlow::Continue(())
        }
        unsafe { walk::<T, A, B, F>(self.root, &mut visit) }
    }
}

#[cfg(test)]
#[path = "avl/tests.rs"]
mod tests;
