use std::{
    alloc::Layout, cell::UnsafeCell, collections::BTreeMap, mem::MaybeUninit, ops::Range,
    prelude::v1::*, ptr::NonNull,
};

#[derive(Debug)]
pub struct ShadowAllocator {
    regions: BTreeMap<usize, SaRegion>,
}

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
pub enum SaRegion {
    Free,
    Used,
    Invalid,
}

impl Default for ShadowAllocator {
    fn default() -> Self {
        Self::new()
    }
}

impl ShadowAllocator {
    pub fn new() -> Self {
        Self {
            regions: Some((0, SaRegion::Invalid)).into_iter().collect(),
        }
    }

    pub fn new_filled_with_free() -> Self {
        Self {
            regions: Some((0, SaRegion::Free)).into_iter().collect(),
        }
    }

    pub fn convert_range(
        &mut self,
        range: Range<usize>,
        old_region: SaRegion,
        new_region: SaRegion,
    ) {
        if range.is_empty() {
            return;
        }

        assert_ne!(old_region, new_region);
        log::trace!(
            "sa: converting {:?} from {:?} to {:?}",
            range,
            old_region,
            new_region
        );

        let (&addr, &region) = self.regions.range(0..range.end).next_back().unwrap();
        if addr > range.start {
            panic!("there's a discontinuity in range {:?}", range);
        } else if region != old_region {
            panic!(
                "range {:?} is {:?} (expected {:?})",
                range, region, old_region
            );
        }

        // Insert an element at `range.start`
        if addr == range.start {
            *self.regions.get_mut(&addr).unwrap() = new_region;
        } else {
            self.regions.insert(range.start, new_region);
        }

        // Each element must represent a discontinuity. If it doesnt't represent
        // a discontinuity, it must be removed.
        if let Some((_, &region)) = self.regions.range(0..range.start).next_back() {
            if region == new_region {
                self.regions.remove(&range.start);
            }
        }

        if let Some(&end_region) = self.regions.get(&range.end) {
            // Each element must represent a discontinuity. If it doesnt't
            // represent a discontinuity, it must be removed.
            if end_region == new_region {
                self.regions.remove(&range.end);
            }
        } else {
            // Insert an element at `range.end`
            self.regions.insert(range.end, old_region);
        }
    }

    pub fn assert_no_pools(&mut self) {
        assert!(
            self.regions.iter().eq(Some((&0, &SaRegion::Invalid))),
            "{:?}",
            self.regions,
        );
    }

    pub fn insert_free_block<T>(&mut self, range: *const [T]) {
        let start = range as *const T as usize;
        let len = unsafe { &*range }.len();
        self.convert_range(start..start + len, SaRegion::Invalid, SaRegion::Free);
    }

    pub fn append_free_block<T>(&mut self, range: *const [T]) {
        let start = range as *const T as usize;
        let mut it = self.regions.range(0..=start).rev();

        assert_eq!(
            it.next(),
            Some((&start, &SaRegion::Invalid)),
            "no boundary at `start`"
        );

        assert_ne!(
            it.next().expect("no previous allocation to append to").1,
            &SaRegion::Invalid,
            "no previous allocation to append to"
        );

        self.insert_free_block(range);
    }

    pub fn remove_pool<T>(&mut self, range: *const [T]) {
        let start = range as *const T as usize;
        // FIXME: Use `<*const [T]>::len` (stabilized in Rust 1.79)
        // FIXME: Or at least `NonNull<[T]>::len` (stabilized in Rust 1.63)
        let end = unsafe { &*(range as *const [MaybeUninit<UnsafeCell<T>>]) }.len() + start;
        if start >= end {
            return;
        }
        log::trace!("sa: invalidating {:?}", start..end);

        // There mustn't be any `Invalid` regions in the range
        for (&addr, &region) in self.regions.range(0..end).rev() {
            if region == SaRegion::Invalid {
                panic!("invalid region at {}", addr);
            }
            if addr <= start {
                break;
            }
        }

        // Create discontinuity at `end` if needed
        {
            let (&addr, &region) = self.regions.range(0..=end).next_back().unwrap();
            if addr < end && region != SaRegion::Invalid {
                self.regions.insert(end, region);
            } else if addr == end && region == SaRegion::Invalid {
                self.regions.remove(&end);
            }
        }

        // Create discontinuity at `start` if needed
        if let Some((_, &region)) = self.regions.range(0..start).next_back() {
            if region != SaRegion::Invalid {
                self.regions.insert(start, SaRegion::Invalid);
            } else {
                self.regions.remove(&start);
            }
        } else {
            assert_eq!(start, 0);
            self.regions.insert(start, SaRegion::Invalid);
        }

        // Remove anything remaining between `start` and `end`
        let keys: Vec<_> = self
            .regions
            .range(start + 1..end)
            .map(|(&addr, _)| addr)
            .collect();
        for key in keys.iter() {
            self.regions.remove(key);
        }
    }

    pub fn allocate(&mut self, layout: Layout, start: NonNull<u8>) {
        let start = start.as_ptr() as usize;
        let len = layout.size();
        assert!(
            start % layout.align() == 0,
            "0x{:x} is not properly aligned (0x{:x} bytes alignment required)",
            start,
            layout.align()
        );
        self.convert_range(start..start + len, SaRegion::Free, SaRegion::Used);
    }

    pub fn deallocate(&mut self, layout: Layout, start: NonNull<u8>) {
        let start = start.as_ptr() as usize;
        let len = layout.size();
        assert!(
            start % layout.align() == 0,
            "0x{:x} is not properly aligned (0x{:x} bytes alignment required)",
            start,
            layout.align()
        );
        self.convert_range(start..start + len, SaRegion::Used, SaRegion::Free);
    }
}
