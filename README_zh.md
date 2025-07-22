<div align="center">
  <img src="./images/logo.png" width="280" />
</div>

\[ [English](README.md) | 简体中文 \]

# 蓝河操作系统内核
蓝河操作系统内核是 vivo 以 Rust 语言自研的内核，简称蓝河内核，具备安全、轻量、通用的核心特性，支持 POSIX 接口和 Rust std。

## 技术架构
具体请查看 vivo 蓝河操作系统官网[内核](https://blueos.vivo.com/kernel)页面。

## 板级支持
蓝河操作系统内核当前支持 ARM32、ARM64、RISCV32、RISCV64 芯片架构
- 支持各芯片架构的 QEMU 模拟器
- 更多的硬件开发板支持正在进行中

## 主要仓库介绍

| 仓库链接 | 描述 |
|---------|------|
| apps | 基于 Rust std 开发的 [shell](https://github.com/vivoblueos/apps_shell) 和 [样例代码](https://github.com/vivoblueos/apps_example) |
| [book](https://github.com/vivoblueos/book) | 内核技术文档和教程，包含详细的内核开发指南 |
| [build](https://github.com/vivoblueos/build) | 项目编译构建模板和脚本 |
| [kernel](https://github.com/vivoblueos/kernel) | 内核核心仓，包括 cpu 架构支持、调度器、同步原语、异步执行器、内存管理子系统、文件系统、网络子系统、设备子系统等 |
| [libc](https://github.com/vivoblueos/libc) | 蓝河操作系统内核的 libc 头文件，fork 自[rust-lang/libc](https://github.com/rust-lang/libc) |
| [librs](https://github.com/vivoblueos/librs) | 蓝河操作系统内核基于 Rust 语言的 libc 实现 |

# 内核开发入门指南
要构建并使用 BlueOS 内核，请查阅以下文档：

- [准备基础构建环境](https://github.com/vivoblueos/book/blob/main/src/getting-started.md)
- [构建定制的 Rust 工具链](https://github.com/vivoblueos/book/blob/main/src/build-rust-toolchain.md)
- [内核开发实践](https://github.com/vivoblueos/book/blob/main/src/build-kernel.md)

# 技术书籍
有关蓝河操作系统内核更多的信息，请参阅[内核开发手册](https://github.com/vivoblueos/book)。
