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

use crate::{
    scheduler, thread,
    thread::ThreadNode,
    time::{
        timer::{
            compare_timer, compute_next_deadline, Comparator, Node, Timer, TimerCallback, TimerMode,
        },
        Tick,
    },
    types::{IntrusiveBinaryHeap, IouIntrusiveBinaryHeapNodeMut},
};

fn execute_callback(tm: &mut Timer) {
    match &mut tm.callback {
        TimerCallback::Nothing => {}
        TimerCallback::Resched(maybe_owner, timeout) => {
            let Some(owner) = maybe_owner.take() else {
                return;
            };
            *timeout = scheduler::queue_ready_thread(thread::SUSPENDED, owner);
        }
        TimerCallback::Do(f) => f(),
        TimerCallback::Posix(f, arg) => f(*arg),
        TimerCallback::UnsafePosix(f, arg) => unsafe { f(*arg) },
    }
}

fn handle_expiration(tm: &mut Timer) {
    if tm.expired() {
        return;
    }
    execute_callback(tm);
    match &mut tm.mode {
        TimerMode::Repeat(r) => {
            r.elapsed_times += 1;
            if let Some(total) = r.total_times
                && r.elapsed_times >= total
            {
                tm.expire();
            }
        }
        _ => tm.expire(),
    }
}

#[derive(Debug)]
pub struct TimerManager {
    timers: IntrusiveBinaryHeap<Timer, Node, Comparator>,
}

pub type Iou<'a> = IouIntrusiveBinaryHeapNodeMut<'a, Timer, Node>;

impl TimerManager {
    pub const fn new() -> Self {
        Self {
            timers: IntrusiveBinaryHeap::<Timer, Node, _>::new(compare_timer),
        }
    }

    pub fn add<'a>(&mut self, tm: &'a mut Timer) -> Option<Iou<'a>> {
        self.timers.push(tm)
    }

    pub fn remove<'a>(&mut self, iou: Iou<'_>) -> Option<Iou<'a>> {
        let tm = IntrusiveBinaryHeap::<Timer, Node, Comparator>::iou_owner(&iou).unwrap();
        self.timers.remove(iou)
    }

    pub fn is_active(&self, iou: &Iou<'_>) -> bool {
        self.timers.is_active(iou)
    }

    pub fn post_expire(&mut self) {
        self.timers.for_each_popped_value(|tm| {
            handle_expiration(tm);
        });
        self.timers
            .move_chosen_popped_values_to_heap(|tm| !tm.expired());
    }

    pub fn expire(&mut self, deadline: Tick) -> usize {
        let mut expired = 0;
        loop {
            let Some(tm) = self.timers.peek() else {
                break;
            };
            let next_deadline = compute_next_deadline(tm);
            if next_deadline > deadline {
                break;
            }
            self.timers.pop();
            expired += 1;
        }
        expired
    }

    pub fn next_deadline(&mut self) -> Option<Tick> {
        let top = self.timers.peek()?;
        Some(compute_next_deadline(top))
    }

    pub fn size(&self) -> usize {
        self.timers.size()
    }
}
