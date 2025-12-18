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

#![no_std]
#![no_main]

extern crate blueos;
extern crate rsrt;

#[no_mangle]
pub extern "C" fn main() -> i32 {
    blueos::kprintln!("Hello, world!");
    let memory_info = blueos::allocator::memory_info();
    blueos::kprintln!(
        "Memory info, total: {}, used: {}, max_used: {}",
        memory_info.total,
        memory_info.used,
        memory_info.max_used
    );
    0
}
