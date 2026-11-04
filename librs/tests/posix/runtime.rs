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

//! Bundling crate for the C POSIX conformance image.
//!
//! `--crate-type staticlib` produces one archive that also contains every
//! dependency's objects, so a second `build_rust()` target over an almost empty
//! root is all that is needed to hand the kernel plus librs to the C linker.
//! The image itself is entered from `runner.c`, which registers itself in
//! `.bk_app_array` and calls `__librs_start_main()`.
//!
//! Nothing must be defined here that would become a second entry point.
//! `//kernel/rsrt` is linked for its global allocator and panic handler only -
//! the `no_app_entry` build of it, because the default one registers an app
//! entry of its own and the case list would then run twice.

#![no_std]
// The point of the crate is the archives it brings along, not the code it
// uses, so both crates are linked but never named.
#![allow(unused_extern_crates)]

extern crate librs;
extern crate rsrt;
