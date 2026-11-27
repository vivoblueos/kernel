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

//! Zero-sized field types for controlling automatic [`Send`] and [`Sync`] implementations.

use core::marker::PhantomData;

// PhantomData<*mut ()> suppresses both auto traits.
pub struct NotThreadSafeMarker(PhantomData<*mut ()>);

pub struct NotSyncMarker(PhantomData<*mut ()>);
unsafe impl Send for NotSyncMarker {}

pub struct NotSendMarker(PhantomData<*mut ()>);
unsafe impl Sync for NotSendMarker {}

// Use these aliases as field types, e.g. `_not_sync: NotSync`.
pub type NotSync = PhantomData<NotSyncMarker>;
pub type NotThreadSafe = PhantomData<NotThreadSafeMarker>;
pub type NotSend = PhantomData<NotSendMarker>;

// Use the same-named constants to initialize marker fields.
#[allow(non_upper_case_globals)]
pub const NotSend: NotSend = PhantomData;
#[allow(non_upper_case_globals)]
pub const NotSync: NotSync = PhantomData;
#[allow(non_upper_case_globals)]
pub const NotThreadSafe: NotThreadSafe = PhantomData;
