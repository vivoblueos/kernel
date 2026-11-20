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

//! Marker types for expressing thread contracts.

use core::marker::PhantomData;

/// A zero-sized field that prevents automatic `Send` and `Sync` implementations.
///
/// Use this for guards that must stay in their acquiring execution context.
/// A containing type may explicitly implement `Sync` if sharing references to it
/// is safe, while leaving ownership transfer disabled.
pub type NotThreadSafe = PhantomData<*mut ()>;

/// Constructs a [`NotThreadSafe`](type@NotThreadSafe) marker.
#[allow(non_upper_case_globals)]
pub const NotThreadSafe: NotThreadSafe = PhantomData;
