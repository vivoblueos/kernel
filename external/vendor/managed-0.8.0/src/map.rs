use core::mem;
use core::fmt;
use core::slice;
use core::borrow::Borrow;
use core::ops::{Bound, RangeBounds};

#[cfg(feature = "std")]
use std::collections::BTreeMap;
#[cfg(feature = "std")]
use std::collections::btree_map::{Iter as BTreeIter, IterMut as BTreeIterMut,
                                  Range as BTreeRange};
#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::collections::btree_map::BTreeMap;
#[cfg(all(feature = "alloc", not(feature = "std")))]
use alloc::collections::btree_map::{Iter as BTreeIter, IterMut as BTreeIterMut,
                                    Range as BTreeRange};

/// A managed map.
///
/// This enum can be used to represent exclusive access to maps.
/// In Rust, exclusive access to an object is obtained by either owning the object,
/// or owning a mutable pointer to the object; hence, "managed".
///
/// The purpose of this enum is providing good ergonomics with `std` present while making
/// it possible to avoid having a heap at all (which of course means that `std` is not present).
/// To achieve this, the variants other than `Borrow` are only available when the corresponding
/// feature is opted in.
///
/// Unlike [Managed](enum.Managed.html) and [ManagedSlice](enum.ManagedSlice.html),
/// the managed map is implemented using a B-tree map when allocation is available,
/// and a sorted slice of key-value pairs when it is not. Thus, algorithmic complexity
/// of operations on it depends on the kind of map.
///
/// A function that requires a managed object should be generic over an `Into<ManagedMap<'a, T>>`
/// argument; then, it will be possible to pass either a `Vec<T>`, or a `&'a mut [T]`
/// without any conversion at the call site.
///
/// See also [Managed](enum.Managed.html).
pub enum ManagedMap<'a, K: 'a, V: 'a> {
    /// Borrowed variant.
    Borrowed(&'a mut [Option<(K, V)>]),
    /// Owned variant, only available with the `std` or `alloc` feature enabled.
    #[cfg(any(feature = "std", feature = "alloc"))]
    Owned(BTreeMap<K, V>)
}

impl<'a, K: 'a, V: 'a> fmt::Debug for ManagedMap<'a, K, V>
        where K: fmt::Debug, V: fmt::Debug {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &ManagedMap::Borrowed(ref x) => write!(f, "Borrowed({:?})", x),
            #[cfg(any(feature = "std", feature = "alloc"))]
            &ManagedMap::Owned(ref x)    => write!(f, "Owned({:?})", x)
        }
    }
}

impl<'a, K: 'a, V: 'a> From<&'a mut [Option<(K, V)>]> for ManagedMap<'a, K, V> {
    fn from(value: &'a mut [Option<(K, V)>]) -> Self {
        ManagedMap::Borrowed(value)
    }
}

#[cfg(any(feature = "std", feature = "alloc"))]
impl<'a, K: 'a, V: 'a> From<BTreeMap<K, V>> for ManagedMap<'a, K, V> {
    fn from(value: BTreeMap<K, V>) -> Self {
        ManagedMap::Owned(value)
    }
}

/// Like `Option`, but with `Some` values sorting first.
#[derive(PartialEq, Eq, PartialOrd, Ord)]
enum RevOption<T> {
    Some(T),
    None
}

impl<T> From<Option<T>> for RevOption<T> {
    fn from(other: Option<T>) -> Self {
        match other {
            Some(x) => RevOption::Some(x),
            None => RevOption::None
        }
    }
}

impl<T> Into<Option<T>> for RevOption<T> {
    fn into(self) -> Option<T> {
        match self {
            RevOption::Some(x) => Some(x),
            RevOption::None => None
        }
    }
}

#[derive(Debug, Clone)]
enum RangeInner<'a, K: 'a, V: 'a> {
    /// Borrowed variant.
    Borrowed { slice: &'a [Option<(K, V)>], begin: usize, end: usize },
    /// Owned variant, only available with the `std` or `alloc` feature enabled.
    #[cfg(any(feature = "std", feature = "alloc"))]
    Owned(BTreeRange<'a, K, V>),
}

#[derive(Debug, Clone)]
pub struct Range<'a, K: 'a, V: 'a>(RangeInner<'a, K, V>);

impl<'a, K: 'a, V: 'a> Iterator for Range<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        match self.0 {
            RangeInner::Borrowed { ref slice, ref mut begin, ref end } => {
                *begin += 1;
                if *begin-1 >= *end {
                    None
                } else {
                    match slice[*begin-1] {
                        None => None,
                        Some((ref k, ref v)) => Some((k, v))
                    }
                }
            },
            #[cfg(any(feature = "std", feature = "alloc"))]
            RangeInner::Owned(ref mut range) => range.next(),
        }
    }
}

impl<'a, K: 'a, V: 'a> DoubleEndedIterator for Range<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        match self.0 {
            RangeInner::Borrowed { ref slice, ref begin, ref mut end } => {
                if *begin >= *end {
                    None
                } else {
                    *end -= 1;
                    match slice[*end] {
                        None => None,
                        Some((ref k, ref v)) => Some((k, v))
                    }
                }
            },
            #[cfg(any(feature = "std", feature = "alloc"))]
            RangeInner::Owned(ref mut range) => range.next_back(),
        }
    }
}

fn binary_search_by_key_range<'a, K, V, Q: 'a, R>(slice: &[Option<(K, V)>], range: R) -> Result<(usize, usize), ()>
    where K: Ord + Borrow<Q>, Q: Ord + ?Sized, R: RangeBounds<Q>
{
    if slice.len() == 0 {
        return Err(())
    }
    let (mut left, mut right) = (0, slice.len() - 1);

    macro_rules! key {
        ( $e:expr) => { $e.as_ref().map(|&(ref key, _)| key.borrow()) }
    }

    // We cannot use slice.binary_search_by_key instead of each of the
    // two loops here, because we need the left-most match (for begin) and
    // the right-most match (for end), and the stdlib does not provide
    // any of these guarantees.

    // Find the beginning
    let begin;
    if let Bound::Unbounded = range.start_bound() {
        begin = 0;
    } else {
        macro_rules! is_before_range {
            ( $item: expr) => {
                match &range.start_bound() {
                    Bound::Included(ref key_begin) => $item < Some(key_begin.borrow()),
                    Bound::Excluded(ref key_begin) => $item <= Some(key_begin.borrow()),
                    Bound::Unbounded => unreachable!()
                }
            }
        };
        while left < right {
            let middle = left + (right - left) / 2;
            if is_before_range!(key!(slice[middle])) {
                left = middle + 1;
            } else if middle > 0 && !is_before_range!(key!(slice[middle - 1])) {
                right = middle - 1;
            } else {
                left = middle;
                break
            }
        }
        if left == slice.len() || is_before_range!(key!(slice[left])) {
            return Err(())
        }
        begin = left
    };

    // Find the ending
    let end;
    if let Bound::Unbounded = range.end_bound() {
        end = slice.len()
    } else {
        macro_rules! is_after_range {
            ( $item:expr ) => {
                match &range.end_bound() {
                    Bound::Included(ref key_end) => $item > Some(key_end.borrow()),
                    Bound::Excluded(ref key_end) => $item >= Some(key_end.borrow()),
                    Bound::Unbounded => unreachable!()
                }
            }
        };
        right = slice.len(); // no need to reset left
        while left < right {
            let middle = left + (right - left + 1) / 2;
            if is_after_range!(key!(slice[middle - 1])) {
                right = middle - 1;
            } else if middle < slice.len() && !is_after_range!(key!(slice[middle])) {
                left = middle + 1;
            } else {
                right = middle;
                break
            }
        }
        if right == 0 || is_after_range!(key!(slice[right - 1])) {
            return Err(())
        }
        end = right
    };

    Ok((begin, end))
}

fn binary_search_by_key<K, V, Q>(slice: &[Option<(K, V)>], key: &Q) -> Result<usize, usize>
    where K: Ord + Borrow<Q>, Q: Ord + ?Sized
{
    slice.binary_search_by_key(&RevOption::Some(key), |entry| {
        entry.as_ref().map(|&(ref key, _)| key.borrow()).into()
    })
}

fn pair_by_key<'a, K, Q, V>(slice: &'a [Option<(K, V)>], key: &Q) ->
                           Result<&'a (K, V), usize>
    where K: Ord + Borrow<Q>, Q: Ord + ?Sized
{
    binary_search_by_key(slice, key).map(move |idx| slice[idx].as_ref().unwrap())
}

fn pair_mut_by_key<'a, K, Q, V>(slice: &'a mut [Option<(K, V)>], key: &Q) ->
                               Result<&'a mut (K, V), usize>
    where K: Ord + Borrow<Q>, Q: Ord + ?Sized
{
    binary_search_by_key(slice, key).map(move |idx| slice[idx].as_mut().unwrap())
}

impl<'a, K: Ord + 'a, V: 'a> ManagedMap<'a, K, V> {
    pub fn clear(&mut self) {
        match self {
            &mut ManagedMap::Borrowed(ref mut pairs) => {
                for item in pairs.iter_mut() {
                    *item = None
                }
            },
            #[cfg(any(feature = "std", feature = "alloc"))]
            &mut ManagedMap::Owned(ref mut map) => map.clear()
        }
    }

    pub fn get<Q>(&self, key: &Q) -> Option<&V>
        where K: Borrow<Q>, Q: Ord + ?Sized
    {
        match self {
            &ManagedMap::Borrowed(ref pairs) => {
                match pair_by_key(pairs, key.borrow()) {
                    Ok(&(_, ref value)) => Some(value),
                    Err(_) => None
                }
            },
            #[cfg(any(feature = "std", feature = "alloc"))]
            &ManagedMap::Owned(ref map) => map.get(key)
        }
    }

    pub fn get_mut<Q>(&mut self, key: &Q) -> Option<&mut V>
        where K: Borrow<Q>, Q: Ord + ?Sized
    {
        match self {
            &mut ManagedMap::Borrowed(ref mut pairs) => {
                match pair_mut_by_key(pairs, key.borrow()) {
                    Ok(&mut (_, ref mut value)) => Some(value),
                    Err(_) => None
                }
            },
            #[cfg(any(feature = "std", feature = "alloc"))]
            &mut ManagedMap::Owned(ref mut map) => map.get_mut(key)
        }
    }

    pub fn range<'b, 'c, Q: 'c, R>(&'b self, range: R) -> Range<'a, K, V>
            where K: Borrow<Q>, Q: Ord + ?Sized, R: RangeBounds<Q>, 'b: 'a
    {
        match self {
            &ManagedMap::Borrowed(ref pairs) => {
                match binary_search_by_key_range(&pairs[0..self.len()], range) {
                    Ok((begin, end)) => Range(RangeInner::Borrowed {
                        slice: &pairs[begin..end], begin: 0, end: end-begin }),
                    Err(()) => Range(RangeInner::Borrowed {
                        slice: &[], begin: 0, end: 0 }),
                }
            },
            #[cfg(any(feature = "std", feature = "alloc"))]
            &ManagedMap::Owned(ref map) => {
                Range(RangeInner::Owned(map.range(range)))
            },
        }
    }

    pub fn insert(&mut self, key: K, new_value: V) -> Result<Option<V>, (K, V)> {
        match self {
            &mut ManagedMap::Borrowed(ref mut pairs) if pairs.len() < 1 =>
                Err((key, new_value)), // no space at all
            &mut ManagedMap::Borrowed(ref mut pairs) => {
                match binary_search_by_key(pairs, &key) {
                    Err(_) if pairs[pairs.len() - 1].is_some() =>
                        Err((key, new_value)), // full
                    Err(idx) => {
                        let rotate_by = pairs.len() - idx - 1;
                        pairs[idx..].rotate_left(rotate_by);
                        assert!(pairs[idx].is_none(), "broken invariant");
                        pairs[idx] = Some((key, new_value));
                        Ok(None)
                    }
                    Ok(idx) => {
                        let mut swap_pair = Some((key, new_value));
                        mem::swap(&mut pairs[idx], &mut swap_pair);
                        let (_key, value) = swap_pair.expect("broken invariant");
                        Ok(Some(value))
                    }
                }
            },
            #[cfg(any(feature = "std", feature = "alloc"))]
            &mut ManagedMap::Owned(ref mut map) => Ok(map.insert(key, new_value))
        }
    }

    pub fn remove<Q>(&mut self, key: &Q) -> Option<V>
        where K: Borrow<Q>, Q: Ord + ?Sized
    {
        match self {
            &mut ManagedMap::Borrowed(ref mut pairs) => {
                match binary_search_by_key(pairs, key) {
                    Ok(idx) => {
                        let (_key, value) = pairs[idx].take().expect("broken invariant");
                        pairs[idx..].rotate_left(1);
                        Some(value)
                    }
                    Err(_) => None
                }
            },
            #[cfg(any(feature = "std", feature = "alloc"))]
            &mut ManagedMap::Owned(ref mut map) => map.remove(key)
        }
    }

    /// ManagedMap contains no elements?
    pub fn is_empty(&self) -> bool {
        match self {
            &ManagedMap::Borrowed(ref pairs) =>
                pairs.iter().all(|item| item.is_none()),
            #[cfg(any(feature = "std", feature = "alloc"))]
            &ManagedMap::Owned(ref map) =>
                map.is_empty()
        }
    }

    /// Returns the number of elements in the ManagedMap.
    pub fn len(&self) -> usize {
        match self {
            &ManagedMap::Borrowed(ref pairs) =>
                pairs.iter()
                .take_while(|item| item.is_some())
                .count(),
            #[cfg(any(feature = "std", feature = "alloc"))]
            &ManagedMap::Owned(ref map) =>
                map.len()
        }
    }

    pub fn iter(&self) -> Iter<K, V> {
        match self {
            &ManagedMap::Borrowed(ref pairs) =>
                Iter::Borrowed(pairs.iter()),
            #[cfg(any(feature = "std", feature = "alloc"))]
            &ManagedMap::Owned(ref map) =>
                Iter::Owned(map.iter()),
        }
    }

    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        match self {
            &mut ManagedMap::Borrowed(ref mut pairs) =>
                IterMut::Borrowed(pairs.iter_mut()),
            #[cfg(any(feature = "std", feature = "alloc"))]
            &mut ManagedMap::Owned(ref mut map) =>
                IterMut::Owned(map.iter_mut()),
        }
    }
}

pub enum Iter<'a, K: 'a, V: 'a> {
    /// Borrowed variant.
    Borrowed(slice::Iter<'a, Option<(K, V)>>),
    /// Owned variant, only available with the `std` or `alloc` feature enabled.
    #[cfg(any(feature = "std", feature = "alloc"))]
    Owned(BTreeIter<'a, K, V>),
}

impl<'a, K: Ord + 'a, V: 'a> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            &mut Iter::Borrowed(ref mut iter) =>
                match iter.next() {
                    Some(&Some((ref k, ref v))) => Some((&k, &v)),
                    Some(&None) => None,
                    None => None,
                },
            #[cfg(any(feature = "std", feature = "alloc"))]
            &mut Iter::Owned(ref mut iter) =>
                iter.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            &Iter::Borrowed(ref iter) => {
                let len = iter.clone()
                    .take_while(|item| item.is_some())
                    .count();
                (len, Some(len))
            },
            #[cfg(any(feature = "std", feature = "alloc"))]
            &Iter::Owned(ref iter) =>
                iter.size_hint(),
        }
    }
}

pub enum IterMut<'a, K: 'a, V: 'a> {
    /// Borrowed variant.
    Borrowed(slice::IterMut<'a, Option<(K, V)>>),
    /// Owned variant, only available with the `std` or `alloc` feature enabled.
    #[cfg(any(feature = "std", feature = "alloc"))]
    Owned(BTreeIterMut<'a, K, V>),
}

impl<'a, K: Ord + 'a, V: 'a> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            &mut IterMut::Borrowed(ref mut iter) =>
                match iter.next() {
                    Some(&mut Some((ref k, ref mut v))) => Some((&k, v)),
                    Some(&mut None) => None,
                    None => None,
                },
            #[cfg(any(feature = "std", feature = "alloc"))]
            &mut IterMut::Owned(ref mut iter) =>
                iter.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            &IterMut::Borrowed(ref iter) => {
                let (_, upper) = iter.size_hint();
                (0, upper)
            },
            #[cfg(any(feature = "std", feature = "alloc"))]
            &IterMut::Owned(ref iter) =>
                iter.size_hint(),
        }
    }
}

// LCOV_EXCL_START
#[cfg(test)]
mod test {
    use super::ManagedMap;
    use core::ops::Bound::*;

    fn all_pairs_empty() -> [Option<(&'static str, u32)>; 4] {
        [None; 4]
    }

    fn one_pair_full() -> [Option<(&'static str, u32)>; 4] {
        [Some(("a", 1)), None, None, None]
    }

    fn all_pairs_full() -> [Option<(&'static str, u32)>; 4] {
        [Some(("a", 1)), Some(("b", 2)), Some(("c", 3)), Some(("d", 4))]
    }

    fn unwrap<'a, K, V>(map: &'a ManagedMap<'a, K, V>) -> &'a [Option<(K, V)>] {
        match map {
            &ManagedMap::Borrowed(ref map) => map,
            _ => unreachable!()
        }
    }

    #[test]
    fn test_clear() {
        let mut pairs = all_pairs_full();
        let mut map = ManagedMap::Borrowed(&mut pairs);
        map.clear();
        assert!(map.is_empty());
        assert_eq!(map.len(), 0);
        assert_eq!(unwrap(&map), all_pairs_empty());
    }

    #[test]
    fn test_get_some() {
        let mut pairs = all_pairs_full();
        let map = ManagedMap::Borrowed(&mut pairs);
        assert_eq!(map.len(), 4);
        assert_eq!(map.get("a"), Some(&1));
        assert_eq!(map.get("b"), Some(&2));
        assert_eq!(map.get("c"), Some(&3));
        assert_eq!(map.get("d"), Some(&4));
    }

    #[test]
    fn test_get_some_one_pair() {
        let mut pairs = one_pair_full();
        let map = ManagedMap::Borrowed(&mut pairs);
        assert_eq!(map.len(), 1);
        assert_eq!(map.get("a"), Some(&1));
    }

    #[test]
    fn test_get_none_full() {
        let mut pairs = all_pairs_full();
        let map = ManagedMap::Borrowed(&mut pairs);
        assert_eq!(map.len(), 4);
        assert!(!map.is_empty());
        assert_eq!(map.get("q"), None);
        assert_eq!(map.get("0"), None);
    }

    #[test]
    fn test_get_none() {
        let mut pairs = one_pair_full();
        let map = ManagedMap::Borrowed(&mut pairs);
        assert_eq!(map.len(), 1);
        assert!(!map.is_empty());
        assert_eq!(map.get("0"), None);
        assert_eq!(map.get("q"), None);
    }

    #[test]
    fn test_get_none_empty() {
        let mut pairs = all_pairs_empty();
        let map = ManagedMap::Borrowed(&mut pairs);
        assert_eq!(map.len(), 0);
        assert!(map.is_empty());
        assert_eq!(map.get("q"), None);
    }

    #[test]
    fn test_range_full_unbounded() {
        let mut pairs = all_pairs_full();
        let map = ManagedMap::Borrowed(&mut pairs);
        assert_eq!(map.len(), 4);

        let mut range = map.range("a"..);
        assert_eq!(range.next(), Some((&"a", &1)));
        assert_eq!(range.next(), Some((&"b", &2)));
        assert_eq!(range.next(), Some((&"c", &3)));
        assert_eq!(range.next(), Some((&"d", &4)));
        assert_eq!(range.next(), None);
        assert_eq!(range.next_back(), None);

        let mut range = map.range("a"..);
        assert_eq!(range.next(), Some((&"a", &1)));
        assert_eq!(range.next_back(), Some((&"d", &4)));
        assert_eq!(range.next_back(), Some((&"c", &3)));
        assert_eq!(range.next(), Some((&"b", &2)));
        assert_eq!(range.next_back(), None);
        assert_eq!(range.next(), None);

        let mut range = map.range("b"..);
        assert_eq!(range.next(), Some((&"b", &2)));
        assert_eq!(range.next(), Some((&"c", &3)));
        assert_eq!(range.next(), Some((&"d", &4)));
        assert_eq!(range.next(), None);
        assert_eq!(range.next_back(), None);

        let mut range = map.range("d"..);
        assert_eq!(range.next(), Some((&"d", &4)));
        assert_eq!(range.next(), None);
        assert_eq!(range.next_back(), None);

        let mut range = map.range(.."e");
        assert_eq!(range.next(), Some((&"a", &1)));
        assert_eq!(range.next(), Some((&"b", &2)));
        assert_eq!(range.next(), Some((&"c", &3)));
        assert_eq!(range.next(), Some((&"d", &4)));
        assert_eq!(range.next(), None);
        assert_eq!(range.next_back(), None);

        let mut range = map.range(.."d");
        assert_eq!(range.next(), Some((&"a", &1)));
        assert_eq!(range.next(), Some((&"b", &2)));
        assert_eq!(range.next(), Some((&"c", &3)));
        assert_eq!(range.next(), None);
        assert_eq!(range.next_back(), None);

        let mut range = map.range(.."b");
        assert_eq!(range.next(), Some((&"a", &1)));
        assert_eq!(range.next(), None);
        assert_eq!(range.next_back(), None);

        let mut range = map.range(.."a");
        assert_eq!(range.next(), None);
        assert_eq!(range.next_back(), None);

        let mut range = map.range::<&str, _>(..);
        assert_eq!(range.next(), Some((&"a", &1)));
        assert_eq!(range.next(), Some((&"b", &2)));
        assert_eq!(range.next(), Some((&"c", &3)));
        assert_eq!(range.next(), Some((&"d", &4)));
        assert_eq!(range.next(), None);
        assert_eq!(range.next_back(), None);
    }

    #[test]
    fn test_range_full_exclude_left() {
        let mut pairs = all_pairs_full();
        let map = ManagedMap::Borrowed(&mut pairs);
        assert_eq!(map.len(), 4);

        let mut range = map.range::<&str, _>((Excluded("a"), Excluded("a")));
        assert_eq!(range.next(), None);
        let mut range = map.range::<&str, _>((Excluded("a"), Excluded("b")));
        assert_eq!(range.next(), None);
        let mut range = map.range::<&str, _>((Excluded("a"), Excluded("c")));
        assert_eq!(range.next(), Some((&"b", &2)));
        assert_eq!(range.next(), None);
        let mut range = map.range::<&str, _>((Excluded("a"), Excluded("d")));
        assert_eq!(range.next(), Some((&"b", &2)));
        assert_eq!(range.next(), Some((&"c", &3)));
        assert_eq!(range.next(), None);
        let mut range = map.range::<&str, _>((Excluded("a"), Excluded("e")));
        assert_eq!(range.next(), Some((&"b", &2)));
        assert_eq!(range.next(), Some((&"c", &3)));
        assert_eq!(range.next(), Some((&"d", &4)));
        assert_eq!(range.next(), None);
    }

    #[test]
    fn test_range_full_include_right() {
        let mut pairs = all_pairs_full();
        let map = ManagedMap::Borrowed(&mut pairs);
        assert_eq!(map.len(), 4);

        let mut range = map.range::<&str, _>((Included("b"), Included("a")));
        assert_eq!(range.next(), None);
        let mut range = map.range::<&str, _>((Included("b"), Included("b")));
        assert_eq!(range.next(), Some((&"b", &2)));
        assert_eq!(range.next(), None);
        let mut range = map.range::<&str, _>((Included("b"), Included("c")));
        assert_eq!(range.next(), Some((&"b", &2)));
        assert_eq!(range.next(), Some((&"c", &3)));
        assert_eq!(range.next(), None);
        let mut range = map.range::<&str, _>((Included("b"), Included("d")));
        assert_eq!(range.next(), Some((&"b", &2)));
        assert_eq!(range.next(), Some((&"c", &3)));
        assert_eq!(range.next(), Some((&"d", &4)));
        assert_eq!(range.next(), None);
        let mut range = map.range::<&str, _>((Included("b"), Included("e")));
        assert_eq!(range.next(), Some((&"b", &2)));
        assert_eq!(range.next(), Some((&"c", &3)));
        assert_eq!(range.next(), Some((&"d", &4)));
        assert_eq!(range.next(), None);

        let mut range = map.range::<&str, _>((Included("b"), Included("a")));
        assert_eq!(range.next_back(), None);
        let mut range = map.range::<&str, _>((Included("b"), Included("b")));
        assert_eq!(range.next_back(), Some((&"b", &2)));
        assert_eq!(range.next_back(), None);
        let mut range = map.range::<&str, _>((Included("b"), Included("c")));
        assert_eq!(range.next_back(), Some((&"c", &3)));
        assert_eq!(range.next_back(), Some((&"b", &2)));
        assert_eq!(range.next_back(), None);
        let mut range = map.range::<&str, _>((Included("b"), Included("d")));
        assert_eq!(range.next_back(), Some((&"d", &4)));
        assert_eq!(range.next_back(), Some((&"c", &3)));
        assert_eq!(range.next_back(), Some((&"b", &2)));
        assert_eq!(range.next_back(), None);
        let mut range = map.range::<&str, _>((Included("b"), Included("e")));
        assert_eq!(range.next_back(), Some((&"d", &4)));
        assert_eq!(range.next_back(), Some((&"c", &3)));
        assert_eq!(range.next_back(), Some((&"b", &2)));
        assert_eq!(range.next_back(), None);
    }

    #[test]
    fn test_range_full() {
        let mut pairs = all_pairs_full();
        let map = ManagedMap::Borrowed(&mut pairs);
        assert_eq!(map.len(), 4);

        let mut range = map.range("0".."a");
        assert_eq!(range.next(), None);
        let mut range = map.range("0".."b");
        assert_eq!(range.next(), Some((&"a", &1)));
        assert_eq!(range.next(), None);
        let mut range = map.range("0".."c");
        assert_eq!(range.next(), Some((&"a", &1)));
        assert_eq!(range.next(), Some((&"b", &2)));
        assert_eq!(range.next(), None);
        let mut range = map.range("0".."d");
        assert_eq!(range.next(), Some((&"a", &1)));
        assert_eq!(range.next(), Some((&"b", &2)));
        assert_eq!(range.next(), Some((&"c", &3)));
        assert_eq!(range.next(), None);
        let mut range = map.range("0".."e");
        assert_eq!(range.next(), Some((&"a", &1)));
        assert_eq!(range.next(), Some((&"b", &2)));
        assert_eq!(range.next(), Some((&"c", &3)));
        assert_eq!(range.next(), Some((&"d", &4)));
        assert_eq!(range.next(), None);

        let mut range = map.range("a".."a");
        assert_eq!(range.next(), None);
        let mut range = map.range("a".."b");
        assert_eq!(range.next(), Some((&"a", &1)));
        assert_eq!(range.next(), None);
        let mut range = map.range("a".."c");
        assert_eq!(range.next(), Some((&"a", &1)));
        assert_eq!(range.next(), Some((&"b", &2)));
        assert_eq!(range.next(), None);
        let mut range = map.range("a".."d");
        assert_eq!(range.next(), Some((&"a", &1)));
        assert_eq!(range.next(), Some((&"b", &2)));
        assert_eq!(range.next(), Some((&"c", &3)));
        assert_eq!(range.next(), None);
        let mut range = map.range("a".."e");
        assert_eq!(range.next(), Some((&"a", &1)));
        assert_eq!(range.next(), Some((&"b", &2)));
        assert_eq!(range.next(), Some((&"c", &3)));
        assert_eq!(range.next(), Some((&"d", &4)));
        assert_eq!(range.next(), None);

        let mut range = map.range("b".."a");
        assert_eq!(range.next(), None);
        let mut range = map.range("b".."b");
        assert_eq!(range.next(), None);
        let mut range = map.range("b".."c");
        assert_eq!(range.next(), Some((&"b", &2)));
        assert_eq!(range.next(), None);
        let mut range = map.range("b".."d");
        assert_eq!(range.next(), Some((&"b", &2)));
        assert_eq!(range.next(), Some((&"c", &3)));
        assert_eq!(range.next(), None);
        let mut range = map.range("b".."e");
        assert_eq!(range.next(), Some((&"b", &2)));
        assert_eq!(range.next(), Some((&"c", &3)));
        assert_eq!(range.next(), Some((&"d", &4)));
        assert_eq!(range.next(), None);

        let mut range = map.range("c".."a");
        assert_eq!(range.next(), None);
        let mut range = map.range("c".."b");
        assert_eq!(range.next(), None);
        let mut range = map.range("c".."c");
        assert_eq!(range.next(), None);
        let mut range = map.range("c".."d");
        assert_eq!(range.next(), Some((&"c", &3)));
        assert_eq!(range.next(), None);
        let mut range = map.range("c".."e");
        assert_eq!(range.next(), Some((&"c", &3)));
        assert_eq!(range.next(), Some((&"d", &4)));
        assert_eq!(range.next(), None);

        let mut range = map.range("d".."a");
        assert_eq!(range.next(), None);
        let mut range = map.range("d".."b");
        assert_eq!(range.next(), None);
        let mut range = map.range("d".."c");
        assert_eq!(range.next(), None);
        let mut range = map.range("d".."d");
        assert_eq!(range.next(), None);
        let mut range = map.range("d".."e");
        assert_eq!(range.next(), Some((&"d", &4)));
        assert_eq!(range.next(), None);

        let mut range = map.range("e".."a");
        assert_eq!(range.next(), None);
        let mut range = map.range("e".."b");
        assert_eq!(range.next(), None);
        let mut range = map.range("e".."c");
        assert_eq!(range.next(), None);
        let mut range = map.range("e".."d");
        assert_eq!(range.next(), None);
        let mut range = map.range("e".."e");
        assert_eq!(range.next(), None);
    }

    #[test]
    fn test_range_one_pair() {
        let mut pairs = one_pair_full();
        let map = ManagedMap::Borrowed(&mut pairs);
        assert_eq!(map.len(), 1);

        let mut range = map.range("0".."a");
        assert_eq!(range.next(), None);
        let mut range = map.range("0".."b");
        assert_eq!(range.next(), Some((&"a", &1)));
        assert_eq!(range.next(), None);
        let mut range = map.range("0".."c");
        assert_eq!(range.next(), Some((&"a", &1)));
        assert_eq!(range.next(), None);

        let mut range = map.range("a".."a");
        assert_eq!(range.next(), None);
        let mut range = map.range("a".."b");
        assert_eq!(range.next(), Some((&"a", &1)));
        assert_eq!(range.next(), None);
        let mut range = map.range("a".."c");
        assert_eq!(range.next(), Some((&"a", &1)));
        assert_eq!(range.next(), None);

        let mut range = map.range("b".."a");
        assert_eq!(range.next(), None);
        let mut range = map.range("b".."b");
        assert_eq!(range.next(), None);
        let mut range = map.range("b".."c");
        assert_eq!(range.next(), None);
    }

    #[test]
    fn test_range_empty() {
        let mut pairs = all_pairs_empty();
        let map = ManagedMap::Borrowed(&mut pairs);
        assert_eq!(map.len(), 0);

        let mut range = map.range("b".."a");
        assert_eq!(range.next(), None);
        let mut range = map.range("b".."b");
        assert_eq!(range.next(), None);
        let mut range = map.range("b".."c");
        assert_eq!(range.next(), None);
    }

    #[test]
    fn test_get_mut_some() {
        let mut pairs = all_pairs_full();
        let mut map = ManagedMap::Borrowed(&mut pairs);
        assert_eq!(map.len(), 4);
        assert!(!map.is_empty());
        assert_eq!(map.get_mut("a"), Some(&mut 1));
        assert_eq!(map.get_mut("b"), Some(&mut 2));
        assert_eq!(map.get_mut("c"), Some(&mut 3));
        assert_eq!(map.get_mut("d"), Some(&mut 4));
    }

    #[test]
    fn test_get_mut_none() {
        let mut pairs = one_pair_full();
        let mut map = ManagedMap::Borrowed(&mut pairs);
        assert_eq!(map.get_mut("q"), None);
    }

    #[test]
    fn test_insert_empty() {
        let mut pairs = all_pairs_empty();
        let mut map = ManagedMap::Borrowed(&mut pairs);
        assert_eq!(map.len(), 0);
        assert!(map.is_empty());

        assert_eq!(map.insert("a", 1), Ok(None));
        assert_eq!(map.len(), 1);
        assert!(!map.is_empty());
        assert_eq!(unwrap(&map),       [Some(("a", 1)), None, None, None]);
    }

    #[test]
    fn test_insert_replace() {
        let mut pairs = all_pairs_empty();
        let mut map = ManagedMap::Borrowed(&mut pairs);
        assert_eq!(map.insert("a", 1), Ok(None));
        assert_eq!(map.insert("a", 2), Ok(Some(1)));
        assert_eq!(map.len(), 1);
        assert!(!map.is_empty());
        assert_eq!(unwrap(&map),       [Some(("a", 2)), None, None, None]);
    }

    #[test]
    fn test_insert_full() {
        let mut pairs = all_pairs_full();
        let mut map = ManagedMap::Borrowed(&mut pairs);
        assert_eq!(map.insert("q", 1), Err(("q", 1)));
        assert_eq!(map.len(), 4);
        assert_eq!(unwrap(&map),       all_pairs_full());
    }

    #[test]
    fn test_insert_one() {
        let mut pairs = one_pair_full();
        let mut map = ManagedMap::Borrowed(&mut pairs);
        assert_eq!(map.insert("b", 2), Ok(None));
        assert_eq!(unwrap(&map),       [Some(("a", 1)), Some(("b", 2)), None, None]);
    }

    #[test]
    fn test_insert_shift() {
        let mut pairs = one_pair_full();
        let mut map = ManagedMap::Borrowed(&mut pairs);
        assert_eq!(map.insert("c", 3), Ok(None));
        assert_eq!(map.insert("b", 2), Ok(None));
        assert_eq!(unwrap(&map),       [Some(("a", 1)), Some(("b", 2)), Some(("c", 3)), None]);
    }

    #[test]
    fn test_insert_no_space() {
        // Zero-sized backing store
        let mut map = ManagedMap::Borrowed(&mut []);
        assert_eq!(map.insert("a", 1), Err(("a", 1)));
    }

    #[test]
    fn test_remove_nonexistent() {
        let mut pairs = one_pair_full();
        let mut map = ManagedMap::Borrowed(&mut pairs);
        assert_eq!(map.remove("b"), None);
        assert_eq!(map.len(), 1);
    }

    #[test]
    fn test_remove_one() {
        let mut pairs = all_pairs_full();
        let mut map = ManagedMap::Borrowed(&mut pairs);
        assert_eq!(map.remove("a"), Some(1));
        assert_eq!(map.len(), 3);
        assert_eq!(unwrap(&map),    [Some(("b", 2)), Some(("c", 3)), Some(("d", 4)), None]);
    }

    #[test]
    fn test_iter_none() {
        let mut pairs = all_pairs_empty();
        let map = ManagedMap::Borrowed(&mut pairs);
        let mut iter = map.iter();
        assert_eq!(iter.size_hint(), (0, Some(0)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_iter_one() {
        let mut pairs = one_pair_full();
        let map = ManagedMap::Borrowed(&mut pairs);
        let mut iter = map.iter();
        assert_eq!(iter.size_hint(), (1, Some(1)));
        assert_eq!(iter.next(), Some((&"a", &1)));
        assert_eq!(iter.size_hint(), (0, Some(0)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_iter_full() {
        let mut pairs = all_pairs_full();
        let map = ManagedMap::Borrowed(&mut pairs);
        let mut iter = map.iter();
        assert_eq!(iter.size_hint(), (4, Some(4)));
        assert_eq!(iter.next(), Some((&"a", &1)));
        assert_eq!(iter.next(), Some((&"b", &2)));
        assert_eq!(iter.next(), Some((&"c", &3)));
        assert_eq!(iter.next(), Some((&"d", &4)));
        assert_eq!(iter.next(), None);
    }

    #[test]
    fn test_iter_mut_full() {
        let mut pairs = all_pairs_full();
        let mut map = ManagedMap::Borrowed(&mut pairs);

        {
            let mut iter = map.iter_mut();
            assert_eq!(iter.size_hint(), (0, Some(4)));
            for (_k, mut v) in &mut iter {
                *v += 1;
            }
            assert_eq!(iter.size_hint(), (0, Some(0)));
            // Scope for `iter` ends here so that it can be borrowed
            // again with the following `iter`.
        }
        {
            let mut iter = map.iter();
            assert_eq!(iter.next(), Some((&"a", &2)));
            assert_eq!(iter.next(), Some((&"b", &3)));
            assert_eq!(iter.next(), Some((&"c", &4)));
            assert_eq!(iter.next(), Some((&"d", &5)));
            assert_eq!(iter.next(), None);
        }
    }
}
