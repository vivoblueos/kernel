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

use crate::println;
use blueos_scal::bk_syscall;
use blueos_test_macro::test;

pub use blueos_header::syscalls::NR::{Echo, Nop};
#[test]
fn test_syscalls() {
    assert_eq!(bk_syscall!(Nop), 0);
    for i in 0..1024 {
        assert_eq!(bk_syscall!(Echo, i), i);
    }
}
