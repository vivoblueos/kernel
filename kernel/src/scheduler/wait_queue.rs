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
    thread::{Thread, ThreadNode, SUSPENDED},
    types::{impl_simple_intrusive_adapter, Arc, Ilist, IlistHead, IouIlistHeadMut},
};

impl_simple_intrusive_adapter!(OffsetOfWait, WaitEntry, wait_node);

#[derive(Debug)]
pub struct WaitEntry {
    pub wait_node: IlistHead<WaitEntry, OffsetOfWait>,
    pub thread: ThreadNode,
}

impl WaitEntry {
    pub fn new(thread: ThreadNode) -> Self {
        Self {
            wait_node: IlistHead::new(),
            thread,
        }
    }
}

impl !Send for WaitEntry {}
impl !Sync for WaitEntry {}

pub type WaitQueue = Ilist<WaitEntry, OffsetOfWait>;

pub fn insert<'a>(
    wq: &mut WaitQueue,
    wait_entry: &'a mut WaitEntry,
    mode: InsertMode,
) -> Option<IouIlistHeadMut<'a, WaitEntry, OffsetOfWait>> {
    match mode {
        InsertMode::InsertByPrio => wq.push_by(compare_priority, wait_entry),
        _ => wq.push(wait_entry),
    }
}

pub fn wake_up_all(wq: &mut WaitQueue) -> usize {
    let mut woken = 0;
    for entry in wq.iter() {
        let t = entry.thread.clone();
        if !scheduler::queue_ready_thread(SUSPENDED, t).is_ok() {
            continue;
        }
        woken += 1;
    }
    woken
}

#[inline]
pub(crate) fn compare_priority(lhs: &WaitEntry, rhs: &WaitEntry) -> core::cmp::Ordering {
    lhs.thread.priority().cmp(&rhs.thread.priority())
}
