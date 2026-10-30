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

#[cfg(not(direct_syscall_handler))]
pub mod platform;

#[cfg(not(direct_syscall_handler))]
#[macro_export]
macro_rules! bk_syscall {
    ($nr:expr) => {
        unsafe { $crate::platform::syscall0($nr as usize) }
    };
    ($nr:expr, $a1:expr) => {
        unsafe { $crate::platform::syscall1($nr as usize, $a1 as usize) }
    };
    ($nr:expr, $a1:expr, $a2:expr) => {
        unsafe { $crate::platform::syscall2($nr as usize, $a1 as usize, $a2 as usize) }
    };
    ($nr:expr, $a1:expr, $a2:expr, $a3:expr) => {
        unsafe {
            $crate::platform::syscall3($nr as usize, $a1 as usize, $a2 as usize, $a3 as usize)
        }
    };
    ($nr:expr, $a1:expr, $a2:expr, $a3:expr, $a4:expr) => {
        unsafe {
            $crate::platform::syscall4(
                $nr as usize,
                $a1 as usize,
                $a2 as usize,
                $a3 as usize,
                $a4 as usize,
            )
        }
    };
    ($nr:expr, $a1:expr, $a2:expr, $a3:expr, $a4:expr, $a5:expr) => {
        unsafe {
            $crate::platform::syscall5(
                $nr as usize,
                $a1 as usize,
                $a2 as usize,
                $a3 as usize,
                $a4 as usize,
                $a5 as usize,
            )
        }
    };
    ($nr:expr, $a1:expr, $a2:expr, $a3:expr, $a4:expr, $a5:expr, $a6:expr) => {
        unsafe {
            $crate::platform::syscall6(
                $nr as usize,
                $a1 as usize,
                $a2 as usize,
                $a3 as usize,
                $a4 as usize,
                $a5 as usize,
                $a6 as usize,
            )
        }
    };
}

#[cfg(direct_syscall_handler)]
pub use blueos::bk_syscall;
