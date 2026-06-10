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

use crate::types::{Arc, ArcInner};

pub mod heap;
pub mod page;

#[cfg(test)]
mod tests;

use heap::BuddyAllocator;

#[allow(non_snake_case)]
mod BUDDY_ALLOC {
    use super::*;

    static CTRL_BLOCK: ArcInner<BuddyAllocator> = ArcInner::new(BuddyAllocator::new());
    pub(in crate::allocator) static PTR: Arc<BuddyAllocator> =
        unsafe { Arc::from_static_inner_ref(&CTRL_BLOCK) };
}

pub(super) use BUDDY_ALLOC::PTR as BUDDY_ALLOC;
