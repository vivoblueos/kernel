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

use crate::time::Tick;

/// Alignment decision output: the deadline the new timer should snap to.
pub struct AlignedStart {
    pub deadline: Tick,
}

/// Next anchor grid deadline (smallest grid point >= now).
pub fn next_anchor_deadline(anchor_last: Tick, period: Tick, now: Tick) -> Tick {
    if now.0 <= anchor_last.0 {
        return anchor_last;
    }
    let elapsed = now.0 - anchor_last.0;
    let steps = elapsed.div_ceil(period.0);
    Tick(anchor_last.0.saturating_add(steps.saturating_mul(period.0)))
}

/// Nearest anchor grid point to `original`, never in the past relative to `now`.
///
/// B's `base_deadline` is the timer's first fire time (a future tick), not the
/// grid origin as in A's rolling model. Snapping must therefore target the grid
/// point nearest the newcomer's intended first fire — which may lie before it
/// (firing a few ticks early to coalesce) — rather than the first grid point
/// after the wall-clock `now`. If that nearest point has already passed, the
/// result advances to the first grid point >= `now` instead.
pub fn nearest_anchor_deadline(anchor_base: Tick, period: Tick, original: Tick, now: Tick) -> Tick {
    if original.0 <= anchor_base.0 {
        return anchor_base;
    }
    let offset = original.0 - anchor_base.0;
    let k = offset / period.0;
    let lower = Tick(anchor_base.0.saturating_add(k.saturating_mul(period.0)));
    let upper = Tick(lower.0.saturating_add(period.0));
    let nearest = if original.0 - lower.0 <= upper.0 - original.0 {
        lower
    } else {
        upper
    };
    if nearest.0 >= now.0 {
        nearest
    } else {
        next_anchor_deadline(anchor_base, period, now)
    }
}

/// `|aligned - original| <= tolerance` (saturating).
pub fn within_tolerance(aligned: Tick, original: Tick, tol: usize) -> bool {
    let diff = aligned.0.abs_diff(original.0);
    diff <= tol
}

/// Scan candidate anchors `(base_deadline, period)` and return the deadline the
/// new timer should snap to, if any.
///
/// An anchor qualifies when its period is an integer multiple/divisor of the
/// new period and the snapped deadline is within `tolerance` of the original.
/// Among qualifiers the smallest period-ratio wins; the result is never in the
/// past. Returns `None` if no anchor qualifies.
pub fn decide_align(
    new_period: Tick,
    new_original_deadline: Tick,
    now: Tick,
    tolerance: usize,
    anchors: impl Iterator<Item = (Tick, Tick)>,
) -> Option<AlignedStart> {
    let mut best: Option<(usize, Tick)> = None; // (ratio, aligned_deadline)
    for (anchor_last, anchor_period) in anchors {
        if anchor_period.0 == 0 || new_period.0 == 0 {
            continue;
        }
        // Integer-multiple/divisor relation.
        let divisible = if new_period.0 >= anchor_period.0 {
            new_period.0.is_multiple_of(anchor_period.0)
        } else {
            anchor_period.0.is_multiple_of(new_period.0)
        };
        if !divisible {
            continue;
        }
        let ratio = if new_period.0 >= anchor_period.0 {
            new_period.0 / anchor_period.0
        } else {
            anchor_period.0 / new_period.0
        };
        let aligned =
            nearest_anchor_deadline(anchor_last, anchor_period, new_original_deadline, now);
        if !within_tolerance(aligned, new_original_deadline, tolerance) {
            continue;
        }
        match best {
            Some((cur_ratio, _)) if cur_ratio <= ratio => {}
            _ => best = Some((ratio, aligned)),
        }
    }
    best.map(|(_, d)| AlignedStart { deadline: d })
}

#[cfg(test)]
mod tests {
    use super::*;
    use blueos_test_macro::test;

    #[test]
    fn same_period_immediate_snap() {
        // anchor p=10 last=0; new p=10; now=20; tol=2. Grid=20, |20-22|=2<=2 -> snap to 20.
        let anchors = [(Tick(0), Tick(10))];
        let res = decide_align(Tick(10), Tick(22), Tick(20), 2, anchors.into_iter());
        assert!(res.is_some());
        assert_eq!(res.unwrap().deadline, Tick(20));
    }

    #[test]
    fn integer_multiple_aligns() {
        // anchor p=40 last=0; new p=20 (x2); now=0; tol=5. Grid=0, |0-3|=3<=5.
        let anchors = [(Tick(0), Tick(40))];
        let res = decide_align(Tick(20), Tick(3), Tick(0), 5, anchors.into_iter());
        assert!(res.is_some());
        assert_eq!(res.unwrap().deadline, Tick(0));
    }

    #[test]
    fn divisor_aligns() {
        // anchor p=20 last=0; new p=40 (x2, new is multiple); now=0; tol=5.
        let anchors = [(Tick(0), Tick(20))];
        let res = decide_align(Tick(40), Tick(3), Tick(0), 5, anchors.into_iter());
        assert!(res.is_some());
        assert_eq!(res.unwrap().deadline, Tick(0));
    }

    #[test]
    fn non_integer_relation_no_align() {
        // 13 vs 8: 13%8!=0 and 8%13!=0 -> skip.
        let anchors = [(Tick(0), Tick(13))];
        let res = decide_align(Tick(8), Tick(5), Tick(0), 10, anchors.into_iter());
        assert!(res.is_none());
    }

    #[test]
    fn out_of_window_no_align() {
        // last=5 p=10 now=10 -> grid=15; |15-20|=5>tol=2 -> None.
        let anchors = [(Tick(5), Tick(10))];
        let res = decide_align(Tick(10), Tick(20), Tick(10), 2, anchors.into_iter());
        assert!(res.is_none());
    }

    #[test]
    fn zero_tolerance_exact_only() {
        // tol=0; grid=30; original=30 -> exact snap.
        let anchors = [(Tick(0), Tick(10))];
        let res = decide_align(Tick(10), Tick(30), Tick(25), 0, anchors.into_iter());
        assert!(res.is_some());
        assert_eq!(res.unwrap().deadline, Tick(30));
    }

    #[test]
    fn zero_tolerance_non_exact_no_align() {
        let anchors = [(Tick(0), Tick(10))];
        let res = decide_align(Tick(10), Tick(29), Tick(25), 0, anchors.into_iter());
        assert!(res.is_none());
    }

    #[test]
    fn min_ratio_preferred() {
        // Two qualified anchors: p=20 (ratio=1) and p=40 (ratio=2). Pick smaller ratio (p=20).
        // now=0, both last=0, grid=0; original=0, |0-0|=0<=5.
        let anchors = [(Tick(0), Tick(20)), (Tick(0), Tick(40))];
        let res = decide_align(Tick(20), Tick(0), Tick(0), 5, anchors.into_iter());
        assert!(res.is_some());
        // ratio=1 anchor (p=20) selected, grid=0.
        assert_eq!(res.unwrap().deadline, Tick(0));
    }

    #[test]
    fn empty_anchors_returns_none() {
        let anchors: [(Tick, Tick); 0] = [];
        let res = decide_align(Tick(10), Tick(0), Tick(0), 5, anchors.into_iter());
        assert!(res.is_none());
    }

    #[test]
    fn expired_anchor_pushed_forward() {
        // anchor last=5 p=10; now=28 -> grid=35 (>= now).
        let anchors = [(Tick(5), Tick(10))];
        let res = decide_align(Tick(10), Tick(33), Tick(28), 5, anchors.into_iter());
        assert!(res.is_some());
        assert_eq!(res.unwrap().deadline, Tick(35));
    }

    #[test]
    fn nearest_rounds_down_within_first_half() {
        // anchor base=0 p=10; original=24 -> lower=20 upper=30, 24-20=4 <= 30-24=6 -> nearest 20.
        assert_eq!(
            nearest_anchor_deadline(Tick(0), Tick(10), Tick(24), Tick(0)),
            Tick(20)
        );
    }

    #[test]
    fn nearest_rounds_up_within_second_half() {
        // anchor base=0 p=10; original=27 -> lower=20 upper=30, 27-20=7 > 30-27=3 -> nearest 30.
        assert_eq!(
            nearest_anchor_deadline(Tick(0), Tick(10), Tick(27), Tick(0)),
            Tick(30)
        );
    }

    #[test]
    fn nearest_at_midpoint_rounds_down() {
        // Tie (original=25, equidistant 20 and 30): rounds down to lower.
        assert_eq!(
            nearest_anchor_deadline(Tick(0), Tick(10), Tick(25), Tick(0)),
            Tick(20)
        );
    }

    #[test]
    fn nearest_past_advances_to_future_grid() {
        // base=100 p=10; original=102 -> nearest lower=100 (in the past vs now=105).
        // Falls back to next_anchor_deadline(100, 10, 105) = 110.
        assert_eq!(
            nearest_anchor_deadline(Tick(100), Tick(10), Tick(102), Tick(105)),
            Tick(110)
        );
    }
}
