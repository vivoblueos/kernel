<div align="center">
  <img src="./images/logo.png" width="280" />
</div>

\[ English | [简体中文](README_zh.md) \]

# vivo BlueOS Kernel
vivo BlueOS kernel is developed using the Rust programming language, featuring security, lightweight, and generality. It is compatible with POSIX interfaces and supports Rust std.

## Technical Architecture
For details, please visit the vivo BlueOS official website [kernel](https://blueos.vivo.com/kernel) page.

## Board Support
- vivo BlueOS kernel currently supports arm32, arm64, and riscv chip architectures, along with corresponding qemu platforms
- Support for additional development boards is currently in progress

## Repository Overview

| Repository Link | Description |
|----------------|-------------|
| apps | [Shell](https://github.com/vivoblueos/apps_shell) and [examples](https://github.com/vivoblueos/apps_example) developed based on Rust std |
| [book](https://github.com/vivoblueos/book) | Kernel technical documentation and tutorials, including detailed kernel development guides |
| [build](https://github.com/vivoblueos/build) | Project compilation build templates and scripts |
| [kernel](https://github.com/vivoblueos/kernel) | Core kernel repository, including CPU architecture support, sync/async Executor, file system, network subsystem, device subsystem, etc. |
| [libc](https://github.com/vivoblueos/libc) | vivo BlueOS kernel libc header files, forked from [rust-lang/libc](https://github.com/rust-lang/libc) |
| [librs](https://github.com/vivoblueos/librs) | vivo BlueOS kernel libc implementation based on Rust programming language |

# vivo BlueOS Kernel Toolchain
We have forked the upstream Rust compiler to support vivo BlueOS kernel targeted to `*-vivo-blueos-*` and vivo BlueOS's Rust std.

We'll finally contribute our changes to the upstream repository and make `*-vivo-blueos-*` a supported platform of Rust.

## How to build
Please check [Build Kernel Rust Toolchain](https://github.com/vivoblueos/book/blob/main/src/build-rust-toolchain.md).

# Technical Documentation
For more information about vivo BlueOS kernel, please refer to our [book](https://github.com/vivoblueos/book).
