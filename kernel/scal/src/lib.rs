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
    ($nr:expr_2021) => {
        unsafe { $crate::platform::syscall0($nr as usize) }
    };
    ($nr:expr_2021, $a1:expr_2021) => {
        unsafe { $crate::platform::syscall1($nr as usize, $a1 as usize) }
    };
    ($nr:expr_2021, $a1:expr_2021, $a2:expr_2021) => {
        unsafe { $crate::platform::syscall2($nr as usize, $a1 as usize, $a2 as usize) }
    };
    ($nr:expr_2021, $a1:expr_2021, $a2:expr_2021, $a3:expr_2021) => {
        unsafe {
            $crate::platform::syscall3($nr as usize, $a1 as usize, $a2 as usize, $a3 as usize)
        }
    };
    ($nr:expr_2021, $a1:expr_2021, $a2:expr_2021, $a3:expr_2021, $a4:expr_2021) => {
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
    ($nr:expr_2021, $a1:expr_2021, $a2:expr_2021, $a3:expr_2021, $a4:expr_2021, $a5:expr_2021) => {
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
    ($nr:expr_2021, $a1:expr_2021, $a2:expr_2021, $a3:expr_2021, $a4:expr_2021, $a5:expr_2021, $a6:expr_2021) => {
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
