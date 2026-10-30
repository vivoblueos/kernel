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

use super::Context;
use core::ffi::c_long;

#[inline]
pub fn handle(val: c_long) -> c_long {
    val
}

#[inline]
pub fn handle_context(ctx: &Context) -> usize {
    map_args!(ctx.args, 0, val, c_long);
    handle(val) as usize
}
