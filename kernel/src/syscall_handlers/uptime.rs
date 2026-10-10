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

use super::Context;
use core::ffi::c_long;

#[inline]
pub fn handle() -> c_long {
    // time::now() 返回自系统启动以来经过的时间（Duration）
    crate::time::now().as_millis() as c_long
}

#[inline]
pub fn handle_context(_ctx: &Context) -> usize {
    handle() as usize
}
