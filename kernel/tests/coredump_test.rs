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

//! Coredump integration test.
//!
//! Calls dump_current() with a synthetic CoredumpReason and validates
//! that the coredump machinery completes without panic.

#![no_main]
#![no_std]

extern crate rsrt;
use semihosting::println;

#[no_mangle]
fn main() -> i32 {
    println!("Coredump integration test start...");

    #[cfg(enable_coredump)]
    {
        let reason = blueos::coredump::elf::CoredumpReason {
            signo: 6,       // SIGABRT
            code: 0,
            fault_addr: 0,
            arch_specific: 0,
        };
        let ok = blueos::coredump::dump_current(&reason);
        if ok {
            println!("Coredump generated successfully.");
        } else {
            println!("Coredump skipped (already in progress or disabled).");
        }
    }

    #[cfg(not(enable_coredump))]
    {
        println!("Coredump not enabled in this configuration.");
    }

    println!("Coredump integration test end.");
    0
}