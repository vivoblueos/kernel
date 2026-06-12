// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// ...

#![no_std]
#![feature(naked_functions)]

#[cfg(any(target_arch = "riscv64", target_arch = "riscv32"))]
pub mod riscv;
#[cfg(any(target_arch = "riscv64", target_arch = "riscv32"))]
pub use riscv::*;