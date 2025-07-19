<div align="center">
  <img src="./images/logo.png" width="280" />
</div>

\[ [English](README.md) | 简体中文 \]

# vivo BlueOS 内核
蓝河操作系统内核是 vivo 以 Rust 语言自研的内核，简称蓝河内核，具备安全、轻量、通用的核心特性，支持 POSIX 接口和 Rust std。

## 技术架构
具体请查看 vivo BlueOS 官网[内核](https://blueos.vivo.com/kernel)页面。

## 板级支持
- vivo BlueOS内核当前支持 arm32、arm64、riscv 芯片架构，和对应的 qemu 平台
- 更多的开发板支持正在进行中

## 主要仓库介绍

| 仓库链接 | 描述 |
|---------|------|
| apps | 基于 Rust std 开发的 [shell](https://github.com/vivoblueos/apps_shell) 和 [样例代码](https://github.com/vivoblueos/apps_example) |
| [book](https://github.com/vivoblueos/book) | 内核技术文档和教程，包含详细的内核开发指南 |
| [build](https://github.com/vivoblueos/build) | 项目编译构建模板和脚本 |
| [kernel](https://github.com/vivoblueos/kernel) | 内核核心仓，包括 cpu 架构支持、sync、async Executor、文件系统、网络子系统、设备子系统等 |
| [libc](https://github.com/vivoblueos/libc) | vivo BlueOS 内核的 libc 头文件，fork 自[rust-lang/libc](https://github.com/rust-lang/libc) |
| [librs](https://github.com/vivoblueos/librs) | vivo BlueOS内核基于 Rust 语言的 libc 实现 |

# vivo BlueOS Kernel Toolchain
我们 fork 了上游 Rust 编译器来支持编译 vivo BlueOS 内核和 Rust std，目标平台为 `*-vivo-blueos-*` 。

我们计划会将我们的更改贡献给上游仓库，并使 `*-vivo-blueos-*` 成为 Rust 官方支持的目标平台。

## How to build
请查看 [构建内核工具链](https://github.com/vivoblueos/book/blob/main/src/build-rust-toolchain.md)。

# 技术书籍
有关 vivo BlueOS 内核更多的信息，请查看我们的[book](https://github.com/vivoblueos/book)。
