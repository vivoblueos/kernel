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

use super::InsertMode;
use crate::{
    scheduler,
    sync::SpinLockGuard,
    thread::{ThreadNode, SUSPENDED},
    types::{impl_simple_intrusive_adapter, Arc, ArcList, IlistHead},
};

impl_simple_intrusive_adapter!(OffsetOfWait, WaitEntry, wait_node);

pub type WaitQueue = ArcList<WaitEntry, OffsetOfWait>;

pub fn insert(wq: &mut WaitQueue, t: ThreadNode, mode: InsertMode) -> bool {
    let e = Arc::new(WaitEntry {
        wait_node: IlistHead::new(),
        thread: t,
    });
    if mode == InsertMode::InsertByPrio {
        return wq.push_by(compare_priority, e);
    }
    wq.push_back(e)
}

pub fn wake_up_all(wq: &mut WaitQueue) -> usize {
    let mut woken = 0;
    while let Some(next) = wq.pop_front() {
        let t = next.thread.clone();
        if let Some(timer) = &t.timer {
            timer.stop();
        }
        let ok = scheduler::queue_ready_thread(SUSPENDED, t);
        debug_assert!(ok);
        woken += 1;
    }
    woken
}

#[derive(Debug)]
pub struct WaitEntry {
    pub wait_node: IlistHead<WaitEntry, OffsetOfWait>,
    pub thread: ThreadNode,
}

impl !Send for WaitEntry {}
impl !Sync for WaitEntry {}

#[inline]
pub(crate) fn compare_priority(lhs: &WaitEntry, rhs: &WaitEntry) -> core::cmp::Ordering {
    lhs.thread.priority().cmp(&rhs.thread.priority())
}

pub(crate) struct WaitQueueGuardDropper<'a, const N: usize> {
    guards: [Option<SpinLockGuard<'a, WaitQueue>>; N],
    num_active_guards: usize,
}

impl<'a, const N: usize> WaitQueueGuardDropper<'a, N> {
    pub const fn const_new() -> Self {
        Self {
            guards: [const { None }; N],
            num_active_guards: 0,
        }
    }

    pub const fn new() -> Self {
        Self::const_new()
    }

    #[inline]
    pub fn add(&mut self, w: SpinLockGuard<'a, WaitQueue>) -> bool {
        if self.num_active_guards == N {
            return false;
        }
        assert!(self.guards[self.num_active_guards].is_none());
        self.guards[self.num_active_guards] = Some(w);
        self.num_active_guards += 1;
        true
    }

    #[inline]
    pub fn forget_irq(&mut self) {
        for i in 0..self.num_active_guards {
            if let Some(v) = self.guards[i].as_mut() {
                v.forget_irq()
            }
        }
    }
}

pub(crate) type DefaultWaitQueueGuardDropper<'a> = WaitQueueGuardDropper<'a, 2>;
