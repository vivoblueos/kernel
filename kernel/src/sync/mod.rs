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

pub mod atomic_wait;
pub use atomic_wait::{atomic_wait, atomic_wake};
pub mod mqueue;
pub mod semaphore;
pub mod spinlock;
pub use mqueue::MessageQueue;
pub use semaphore::Semaphore;
pub use spinlock::{ISpinLock, SpinLock, SpinLockGuard};
#[cfg(event_flags)]
pub mod event_flags;
