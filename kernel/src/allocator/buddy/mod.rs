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

// #[cfg(test)]
// mod tests;

use heap::BuddyAllocator;

#[allow(non_snake_case)]
mod BUDDY_ALLOC {
    use super::*;

    // ArcInner 包含堆上内存（BuddyAllocator）和引用计数，这是一个不可变引用
    static CTRL_BLOCK: ArcInner<BuddyAllocator> = ArcInner::new(BuddyAllocator::new());
    // 用 Arc 包含这个 ArcInner，形成一个全局可访问的 Arc<BuddyAllocator>，并且在编译时初始化
    pub(in crate::allocator) static PTR: Arc<BuddyAllocator> =
        unsafe { Arc::from_static_inner_ref(&CTRL_BLOCK) };
}

// 这里我们将 BUDDY_ALLOC 的 PTR 公开为 BUDDY_ALLOC，这样其他模块就可以通过 allocator::buddy::BUDDY_ALLOC 来访问全局的 BuddyAllocator 实例。
pub(super) use BUDDY_ALLOC::PTR as BUDDY_ALLOC;
