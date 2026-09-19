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

//! Dedicated bootable kernel image for the dynamic shell.
//!
//! Boot initializes the application runtime before the scheduler starts. This
//! image's static entry then installs the system image into the root tmpfs and
//! launches the dynamic bootstrap shell from it, keeping both that seeding and
//! that interactive application out of unrelated test images.

#![no_main]
#![no_std]

extern crate alloc;
extern crate rsrt;

/// Anchor the kernel crate into the link. A boot image without static
/// applications has no application code whose kernel references would pull
/// the kernel objects, and the reset vector table lives inside the kernel's
/// arch module — so without this anchor the linker would garbage-collect the
/// whole kernel out of the image.
#[used]
static KERNEL_ANCHOR: extern "C" fn() -> usize = blueos::arch::current_sp;

#[no_mangle]
pub extern "C" fn main() {
    // Install the system image into the root tmpfs, then start the shell from
    // it. Both belong to this image alone: seeding reads the host over
    // semihosting, so it must not happen in images whose runner has no
    // semihosting handler.
    blueos::application::seed::install();
    blueos::application::runtime::launch_bootstrap_shell();
}
