//! Iterator over the components of an algebraic vector

use super::{Component, Vector};
use core::marker::PhantomData;

/// Iterator over the components of an algebraic vector
#[derive(Clone, Debug)]
pub struct Iter<'a, V, C>
where
    V: Vector<C>,
    C: Component,
{
    /// Reference to the original vector
    vector: &'a V,

    /// Iteration position within the vector
    position: usize,

    /// Component type
    component: PhantomData<C>,
}

impl<'a, V, C> Iter<'a, V, C>
where
    V: Vector<C>,
    C: Component,
{
    /// Create a new iterator over the vector's components
    pub(super) fn new(vector: &'a V) -> Self {
        Self {
            vector,
            position: 0,
            component: PhantomData,
        }
    }
}

impl<'a, V, C> Iterator for Iter<'a, V, C>
where
    V: Vector<C>,
    C: Component,
{
    type Item = C;

    fn next(&mut self) -> Option<C> {
        let item = self.vector.get(self.position);

        if item.is_some() {
            self.position += 1;
        }

        item
    }
}
