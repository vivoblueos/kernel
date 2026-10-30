//! A slotmap, a vector-like container with unique keys instead of indices.
//!
//! See the documentation of [`SlotMap`] for details.
//!
//! [`SlotMap`]: struct.SlotMap.html
use super::{ManagedSlice as Slice};

/// Provides links between slots and elements.
///
/// The benefit of separating this struct from the elements is that it is unconditionally `Copy`
/// and `Default`. It also provides better locality for both the indices and the elements which
/// could help with iteration or very large structs.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Slot {
    /// The id of this slot.
    ///
    /// If the given out index mismatches the `generation_id` then the element was removed already
    /// and we can return `None` on lookup.
    ///
    /// If the slot is currently unused we will instead provide the index to the previous slot in
    /// the slot-free-list.
    generation_id: GenerationOrFreelink,
}

/// Provides a slotmap based on external memory.
///
/// A slotmap provides a `Vec`-like interface where each entry is associated with a stable
/// index-like key. Lookup with the key will detect if an entry has been removed but does not
/// require a lifetime relation. Compared to other slotmap implementations this does not internally
/// allocate any memory on its own but only relies on the [`Slice`] arguments in the constructor.
///
/// [`Slice`]: ../enum.Slice.html
///
/// ## Usage
///
/// The important aspect is that the slotmap does not create the storage of its own elements, it
/// merely manages one given to it at construction time.
///
/// ```
/// # use managed::{ManagedSlice, SlotMap, SlotIndex};
///
/// let mut elements = [0usize; 1024];
/// let mut slots = [SlotIndex::default(); 1024];
///
/// let mut map = SlotMap::new(
///     ManagedSlice::Borrowed(&mut elements[..]),
///     ManagedSlice::Borrowed(&mut slots[..]));
/// let index = map.insert(42).unwrap();
/// assert_eq!(map.get(index).cloned(), Some(42));
/// ```
pub struct SlotMap<'a, T> {
    /// The slice where elements are placed.
    /// All of them are initialized at all times but not all are logically part of the map.
    elements: Slice<'a, T>,
    /// The logical list of used slots.
    /// Note that a slot is never remove from this list but instead used to track the generation_id
    /// and the link in the free list.
    slots: Partial<'a, Slot>,
    /// The source of generation ids.
    /// Generation ids are a positive, non-zero value.
    generation: Generation,
    /// An index to the top element of the free list.
    /// Refers to the one-past-the-end index of `slots` if there are no elements.
    free_top: usize,
    /// An abstraction around computing wrapped indices in the free list.
    indices: IndexComputer,
}

/// A backing slice tracking an index how far it is logically initialized.
struct Partial<'a, T> {
    slice: Slice<'a, T>,
    next_idx: usize,
}

/// An index into a slotmap.
///
/// The index remains valid until the entry is removed. If accessing the slotmap with the index
/// again after the entry was removed will fail, even if the index where the element was previously
/// stored has been reused for another element.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Key {
    idx: usize,
    generation: Generation,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
struct GenerationOrFreelink(isize);

/// Newtype wrapper around the index of a free slot.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
struct FreeIndex(usize);

/// The generation counter.
///
/// Has a strictly positive value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Generation(isize);

/// Offset of a freelist entry to the next entry.
///
/// Has a negative or zero value. Represents the negative of the offset to the next element in the
/// free list, wrapping around at the capacity.
/// The base for the offset is the *next* element for two reasons:
/// * Offset of `0` points to the natural successor.
/// * Offset of `len` would point to the element itself and should not occur.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct Offset(isize);

/// Links FreeIndex and Offset.
struct IndexComputer(usize);

impl<T> SlotMap<'_, T> {
    /// Retrieve a value by index.
    pub fn get(&self, index: Key) -> Option<&T> {
        let slot_generation = self.slots
            .get(index.idx)?
            .generation_id
            .generation().ok()?;

        if slot_generation != index.generation {
            return None;
        }

        self.elements.get(index.idx)
    }

    /// Retrieve a mutable value by index.
    pub fn get_mut(&mut self, index: Key) -> Option<&mut T> {
        let slot_generation = self.slots
            .get(index.idx)?
            .generation_id
            .generation().ok()?;

        if slot_generation != index.generation {
            return None;
        }

        self.elements.get_mut(index.idx)
    }

    /// Reserve a new entry.
    ///
    /// In case of success, the returned key refers to the entry until it is removed. The entry
    /// itself is not initialized with any particular value but instead retains the value it had in
    /// the backing slice. It is only logically placed into the slot map.
    pub fn reserve(&mut self) -> Option<(Key, &mut T)> {
        let index = self.next_free_slot()?;
        let slot = self.slots.get_mut(index.0).unwrap();
        let element = &mut self.elements[index.0];

        let offset = slot.generation_id
            .free_link()
            .expect("Free link should be free");
        slot.generation_id = self.generation.into();
        let key = Key {
            idx: index.0,
            generation: self.generation,
        };

        self.free_top = self.indices.free_list_next(index, offset);
        self.generation.advance();
        Some((key, element))
    }

    /// Try to insert a value into the map.
    ///
    /// This will fail if there is not enough space. Sugar wrapper around `reserve` for inserting
    /// values. Note that on success, an old value stored in the backing slice will be overwritten.
    /// Use `reserve` directly if it is vital that no old value is dropped.
    pub fn insert(&mut self, value: T) -> Option<Key> {
        // Insertion must work but we don't care about the value.
        let (index, element) = self.reserve()?;
        *element = value;
        Some(index)
    }

    /// Remove an element.
    ///
    /// If successful, return a mutable reference to the removed element so that the caller can
    /// swap it with a logically empty value. Returns `None` if the provided index did not refer to
    /// an element that could be freed.
    pub fn remove(&mut self, index: Key) -> Option<&mut T> {
        if self.get(index).is_none() {
            return None
        }

        // The slot can be freed.
        let free = FreeIndex(index.idx);
        let slot = self.slots.get_mut(index.idx).unwrap();
        assert!(slot.generation_id.generation().is_ok());

        let offset = self.indices.free_list_offset(free, self.free_top);
        slot.generation_id = offset.into();
        self.free_top = index.idx;

        Some(&mut self.elements[index.idx])
    }

    /// Get the next free slot.
    fn next_free_slot(&mut self) -> Option<FreeIndex> {
        // If free_top is one-past-the-end marker one of those is going to fail. Note that this
        // also means extracting one of these statements out of the function may change the
        // semantics if `elements.len() != slots.len()`.

        // Ensure the index refers to an element within the slice or try to allocate a new slot
        // wherein we can fit the element.
        let free = match self.slots.get_mut(self.free_top) {
            // There is a free element in our free list.
            Some(_) => {
                // Ensure that there is also a real element there.
                let _= self.elements.get_mut(self.free_top)?;
                FreeIndex(self.free_top)
            },
            // Need to try an get a new element from the slot slice.
            None => { // Try to get the next one
                // Will not actually wrap if pushing is successful.
                let new_index = self.slots.len();
                // Ensure there is an element where we want to push to.
                let _ = self.elements.get_mut(new_index)?;

                let free_slot = self.slots.try_reserve()?;
                let free_index = FreeIndex(new_index);
                // New top is the new one-past-the-end.
                let new_top = new_index.checked_add(1).unwrap();

                let offset = self.indices.free_list_offset(free_index, new_top);
                free_slot.generation_id = offset.into();
                self.free_top = free_index.0;

                free_index
            }
        };


        // index refers to elements within the slices
        Some(free)
    }
}

impl<'a, T> SlotMap<'a, T> {
    /// Create a slot map.
    ///
    /// The capacity is the minimum of the capacity of the element and slot slices.
    pub fn new(elements: Slice<'a, T>, slots: Slice<'a, Slot>) -> Self {
        let capacity = elements.len().min(slots.len());
        SlotMap {
            elements,
            slots: Partial {
                slice: slots,
                next_idx: 0,
            },
            generation: Generation::default(),
            free_top: 0,
            indices: IndexComputer::from_capacity(capacity),
        }
    }
}

impl<'a, T> Partial<'a, T> {
    fn get(&self, idx: usize) -> Option<&T> {
        if idx >= self.next_idx {
            None
        } else {
            Some(&self.slice[idx])
        }
    }

    fn get_mut(&mut self, idx: usize) -> Option<&mut T> {
        if idx >= self.next_idx {
            None
        } else {
            Some(&mut self.slice[idx])
        }
    }

    fn len(&self) -> usize {
        self.next_idx
    }

    fn try_reserve(&mut self) -> Option<&mut T> {
        if self.next_idx == self.slice.len() {
            None
        } else {
            let idx = self.next_idx;
            self.next_idx += 1;
            Some(&mut self.slice[idx])
        }
    }
}

impl GenerationOrFreelink {
    pub(crate) fn free_link(self) -> Result<Offset, Generation> {
        if self.0 > 0 {
            Err(Generation(self.0))
        } else {
            Ok(Offset(self.0))
        }
    }

    pub(crate) fn generation(self) -> Result<Generation, Offset> {
        match self.free_link() {
            Ok(offset) => Err(offset),
            Err(generation) => Ok(generation),
        }
    }
}

impl IndexComputer {
    pub(crate) fn from_capacity(capacity: usize) -> Self {
        assert!(capacity < isize::max_value() as usize);
        IndexComputer(capacity)
    }

    /// Get the next free list entry.
    /// This applies the offset to the base index, wrapping around if required.
    ///
    /// This is the reverse of `free_list_offset`.
    fn free_list_next(&self, FreeIndex(base): FreeIndex, offset: Offset)
        -> usize
    {
        let capacity = self.0;
        let offset = offset.int_offset();

        assert!(base < capacity);
        assert!(offset <= capacity);
        let base = base + 1;

        if capacity - offset >= base {
            offset + base // Fine within the range
        } else {
            // Mathematically, capacity < offset + base < 2*capacity
            // Wrap once, mod (capacity + 1), result again in range
            offset
                .wrapping_add(base)
                .wrapping_sub(capacity + 1)
        }
    }

    /// Get the offset difference between the index and the next element.
    /// Computes a potentially wrapping positive offset where zero is the element following the
    /// base.
    ///
    /// This is the reverse of `free_list_next`.
    fn free_list_offset(&self, FreeIndex(base): FreeIndex, to: usize)
        -> Offset
    {
        let capacity = self.0;

        assert!(base != to, "Cant offset element to itself");
        assert!(base < capacity, "Should never have to offset the end-of-list marker");
        assert!(to <= capacity, "Can only offset to the end-of-list marker");
        let base = base + 1;

        Offset::from_int_offset(if base <= to {
            to - base
        } else {
            // Wrap once, mod (capacity + 1), result again in range
            to
                .wrapping_add(capacity + 1)
                .wrapping_sub(base)
        })
    }
}

impl Generation {
    pub(crate) fn advance(&mut self) {
        assert!(self.0 > 0);
        self.0 = self.0.wrapping_add(1).max(1)
    }
}

impl Offset {
    pub(crate) fn from_int_offset(offset: usize) -> Self {
        assert!(offset < isize::max_value() as usize);
        Offset((offset as isize).checked_neg().unwrap())
    }

    pub(crate) fn int_offset(self) -> usize {
        self.0.checked_neg().unwrap() as usize
    }
}

impl Default for Generation {
    fn default() -> Self {
        Generation(1)
    }
}

impl From<Generation> for GenerationOrFreelink {
    fn from(gen: Generation) -> GenerationOrFreelink {
        GenerationOrFreelink(gen.0)
    }
}

impl From<Offset> for GenerationOrFreelink {
    fn from(offset: Offset) -> GenerationOrFreelink {
        GenerationOrFreelink(offset.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::slice::ManagedSlice as Slice;

    #[test]
    fn simple() {
        let mut elements = [0u32; 2];
        let mut slots = [Slot::default(); 2];

        let mut map = SlotMap::new(
            Slice::Borrowed(&mut elements[..]),
            Slice::Borrowed(&mut slots[..]));
        let key42 = map.insert(42).unwrap();
        let keylo = map.insert('K' as _).unwrap();

        assert_eq!(map.insert(0x9999), None);
        assert_eq!(map.get(key42).cloned(), Some(42));
        assert_eq!(map.get(keylo).cloned(), Some('K' as _));

        assert!(map.remove(key42).is_some());
        assert_eq!(map.get(key42), None);

        let lastkey = map.insert(0x9999).unwrap();
        assert_eq!(map.get(lastkey).cloned(), Some(0x9999));

        *map.remove(keylo).unwrap() = 0;
        assert_eq!(map.get(lastkey).cloned(), Some(0x9999));
        assert!(map.remove(lastkey).is_some());
    }

    #[test]
    fn retained() {
        let mut elements = [0u32; 1];
        let mut slots = [Slot::default(); 1];

        let mut map = SlotMap::new(
            Slice::Borrowed(&mut elements[..]),
            Slice::Borrowed(&mut slots[..]));
        let key = map.insert(0xde).unwrap();
        map.remove(key).unwrap();
        assert_eq!(map.get(key), None);

        let new_key = map.insert(0xad).unwrap();

        assert_eq!(map.get(key), None);
        assert_eq!(map.get(new_key).cloned(), Some(0xad));

        assert_eq!(map.remove(key), None);
        map.remove(new_key).unwrap();

        assert_eq!(map.get(key), None);
        assert_eq!(map.get(new_key), None);
    }

    #[test]
    fn non_simple_free_list() {
        // Check the free list implementation
        let mut elements = [0u32; 3];
        let mut slots = [Slot::default(); 3];

        let mut map = SlotMap::new(
            Slice::Borrowed(&mut elements[..]),
            Slice::Borrowed(&mut slots[..]));

        let key0 = map.insert(0).unwrap();
        let key1 = map.insert(1).unwrap();
        let key2 = map.insert(2).unwrap();

        *map.remove(key1).unwrap() = 0xF;
        assert_eq!(map.free_top, 1);
        assert_eq!(map.get(key0).cloned(), Some(0));
        assert_eq!(map.get(key2).cloned(), Some(2));

        *map.remove(key2).unwrap() = 0xF;
        assert_eq!(map.free_top, 2);
        assert_eq!(map.get(key0).cloned(), Some(0));

        *map.remove(key0).unwrap() = 0xF;
        assert_eq!(map.free_top, 0);

        let key0 = map.insert(0).unwrap();
        assert_eq!(map.free_top, 2);
        let key1 = map.insert(1).unwrap();
        let key2 = map.insert(2).unwrap();
        assert_eq!(map.get(key0).cloned(), Some(0));
        assert_eq!(map.get(key1).cloned(), Some(1));
        assert_eq!(map.get(key2).cloned(), Some(2));
    }
}
