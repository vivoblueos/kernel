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

//! Target-address arithmetic and diagnostic bounds.

use crate::{
    error::{ErrorContext, LoadErrorKind},
    memory::{TargetAddress, TargetRange},
};
use blueos_test_macro::test;

#[test]
fn target_address_difference_returns_a_distance() {
    for (start, end, expected) in [
        (0, 0, 0),
        (0x1000, 0x2000, 0x1000),
        (u64::MAX, u64::MAX, 0),
        (0, u64::MAX, u64::MAX),
    ] {
        let start = TargetAddress::new(start);
        let end = TargetAddress::new(end);
        let distance: u64 = end.checked_sub(start).unwrap();
        assert_eq!(distance, expected);
        assert_eq!(start.checked_add(distance).unwrap(), end);
    }
}

#[test]
fn target_address_underflow_preserves_both_bounds() {
    for (start, end) in [
        (0x2000, 0x1000),
        (1, 0),
        (u64::MAX, 0),
        (u64::MAX, u64::MAX - 1),
    ] {
        let start = TargetAddress::new(start);
        let end = TargetAddress::new(end);
        let error = end.checked_sub(start).unwrap_err();
        assert_eq!(error.kind(), LoadErrorKind::IntegerOverflow);
        assert!(error.stage().is_none());
        assert!(matches!(
            error.context(),
            ErrorContext::TargetBounds { start: actual_start, end: actual_end }
                if *actual_start == start && *actual_end == end
        ));
    }
}

#[test]
fn target_address_addition_overflow_preserves_the_requested_span() {
    for (start, len) in [(u64::MAX, 1), (u64::MAX - 3, 4)] {
        let start = TargetAddress::new(start);
        let error = start.checked_add(len).unwrap_err();
        assert_eq!(error.kind(), LoadErrorKind::IntegerOverflow);
        assert!(matches!(
            error.context(),
            ErrorContext::TargetRange { start: actual_start, len: actual_len, align: 0 }
                if *actual_start == start && *actual_len == len
        ));
    }
}

#[test]
fn target_alignment_checks_rounding_and_overflow() {
    for (value, alignment, down, up) in [
        (0, 1, 0, 0),
        (0x1003, 0x1000, 0x1000, 0x2000),
        (0x2000, 0x1000, 0x2000, 0x2000),
    ] {
        let address = TargetAddress::new(value);
        assert_eq!(address.align_down(alignment).unwrap().get(), down);
        assert_eq!(address.align_up(alignment).unwrap().get(), up);
    }
    for align in [0, 3] {
        assert_eq!(
            TargetAddress::new(1).align_down(align).unwrap_err().kind(),
            LoadErrorKind::InvalidAlignment
        );
        assert_eq!(
            TargetAddress::new(1).align_up(align).unwrap_err().kind(),
            LoadErrorKind::InvalidAlignment
        );
    }
    assert_eq!(
        TargetAddress::new(u64::MAX).align_up(2).unwrap_err().kind(),
        LoadErrorKind::IntegerOverflow
    );
}

#[test]
fn target_ranges_use_checked_half_open_bounds() {
    let range = TargetRange::new(TargetAddress::new(0x1000), 0x100);
    for (start, len, expected) in [
        (0x1000, 0x100, true),
        (0x10ff, 1, true),
        (0x1100, 0, true),
        (0x1100, 1, false),
        (0xfff, 1, false),
        (u64::MAX, 1, false),
    ] {
        assert_eq!(
            range.contains_span(TargetAddress::new(start), len),
            expected
        );
    }
    for (start, len, expected) in [
        (0x1100, 0x100, false),
        (0x10ff, 1, true),
        (0x1000, 0, false),
        (u64::MAX, 1, false),
    ] {
        assert_eq!(
            range.overlaps(TargetRange::new(TargetAddress::new(start), len)),
            expected
        );
    }
    let overflowing = TargetRange::new(TargetAddress::new(u64::MAX), 1);
    assert_eq!(
        overflowing.end().unwrap_err().kind(),
        LoadErrorKind::IntegerOverflow
    );
    assert!(!overflowing.contains_span(TargetAddress::new(u64::MAX), 0));
}
