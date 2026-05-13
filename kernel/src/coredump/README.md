# Coredump 模块使用说明

## 概述

Coredump 模块在设备端生成 ELF ET_CORE 格式的 coredump 文件，包含寄存器状态、内存区域和线程信息，用于事后故障分析。

## 触发方式

Coredump 通过以下方式自动触发：

1. **异常处理** — 当 CPU 触发异常（段错误、总线错误、非法指令等）时，`dump_current()` 由异常处理句柄调用
2. **内核恐慌** — `panic_handler` 调用 `dump_current()` 生成崩溃转储
3. **主动调用** — 代码可直接调用 `coredump::dump_current(&reason)` 或 `coredump::dump(&reason, mode)`

`dump_current()` 表示"转储当前线程"；`dump()` 支持 `DumpMode::Current` 和 `DumpMode::All`。

## 信号映射

架构特定的异常码会被映射为标准信号：

| 架构 | 映射函数 | 输入来源 |
|---|---|---|
| RISC-V | `riscv_mcause_to_signo(mcause)` | mcause CSR |
| AArch64 | `aarch64_ec_to_signo(ec)` | ESR_EL1 EC 字段 |
| Cortex-M | `arm_cfsr_to_signo(cfsr)` | CFSR (MMFSR/BFSR/UFSR) |

参见 [signal.rs](signal.rs) 中的映射表。

## 后端选择（编译时）

后端在编译时通过 Kconfig 和 `#[cfg]` 链选择，优先级：

1. **`CONFIG_COREDUMP_MEM_BACKEND=y`** → MemoryBackend（静态缓冲区）
2. **`CONFIG_ENABLE_VFS=y` 且非 MemoryBackend** → FileBackend（VFS 文件）
3. **非 MemoryBackend 且非 VFS** → LoggingBackend（串口/半主机十六进制输出）

### FileBackend

输出路径格式：`/tmp/blueos.core.<pid>`，其中 pid 为当前线程 ID。

### LoggingBackend

通过半主机（semihosting）逐行输出十六进制编码的 ELF 数据，每行最多 64 个十六进制字符。
末尾添加 trailer：
```
[BLUEOS_COREDUMP_END] mode=Current chunks=N size=NKB
```

### MemoryBackend

将 coredump 写入内核中一个静态缓冲区（`COREDUMP_STORAGE`），缓冲区位于 `.coredump_bss` 链接段，
不会被 BSS 内存区域收集逻辑包含。Coredump 完成后设置 `COREDUMP_VALID` 标志。

## Kconfig 选项

| 选项 | 类型 | 默认值 | 说明 |
|---|---|---|---|
| `ENABLE_COREDUMP` | bool | n | 全局 coredump 开关 |
| `COREDUMP_MEM_BACKEND` | bool | n | 使用 MemoryBackend（依赖 ENABLE_COREDUMP） |
| `COREDUMP_BUF_SIZE` | int | 64KB (Cortex-M) / 256KB (32-bit) / 4MB | ELF 缓冲区大小（字节） |

默认值规则：
- Cortex-M（资源受限）：64KB
- 其他 32 位平台：256KB
- 64 位平台：4MB

## 集成测试

```bash
# 运行 coredump 集成测试
ninja -C out/qemu_riscv64.debug.swi run_coredump_test
```

测试流程：构造一个 `CoredumpReason { signo: 6, code: 0, fault_addr: 0, arch_specific: 0 }`，
调用 `dump_current()`，验证返回成功并输出 "Coredump integration test end."。

测试断言定义在 [tests/coredump.checker](../tests/coredump.checker)：
```
// ASSERT-SUCC: Coredump integration test end.
// ASSERT-FAIL: Backtrace in Panic.*
```

## 串口日志解析工具

当使用 LoggingBackend 时，coredump 数据以十六进制格式输出到串口/半主机。使用解析工具还原为 `.core` ELF 文件：

```bash
# 从 QEMU 串口日志解析
python3 tools/coredump_parser.py < qemu_log.txt -o blueos.core

# 指定输入文件
python3 tools/coredump_parser.py --input qemu_log.txt -o blueos.core

# 验证生成的 core 文件
python3 tools/coredump_parser.py --input qemu_log.txt -o blueos.core --validate

# 查看详细信息
python3 tools/coredump_parser.py --input qemu_log.txt -o blueos.core --verbose
```

选项：
- `--input` / `-i`：输入文件（默认 stdin）
- `--output` / `-o`：输出 core 文件路径
- `--validate`：用 `readelf` 验证生成的 core 文件
- `--verbose`：打印元数据和大小信息

## 架构兼容性

| 架构 | 支持状态 | 说明 |
|---|---|---|
| RISC-V 64 | 完全支持 | qemu_riscv64 |
| RISC-V 32 | 完全支持 | qemu_riscv32, gd32vw553_eval |
| AArch64 | 完全支持 | qemu_virt64_aarch64 |
| Cortex-M | 完全支持 | qemu_mps2_an385 |
| ESP32-C3 | 完全支持 | seeed_xiao_esp32c3（RISC-V 32） |

## 注意事项

1. **缓冲区大小**：`COREDUMP_BUF_SIZE` 必须足够容纳完整的 ELF 输出，否则 `write()` 返回错误。
2. **重入保护**：`COREDUMP_IN_PROGRESS` 防止递归触发 coredump。
3. **中断状态**：Coredump 在中断关闭状态下执行（异常处理句柄保证）。
4. **`.coredump_bss` 链接段**：ELF 缓冲区和 MemoryBackend 存储区放在此段中，确保 BSS 内存转储不会包含这些缓冲区自身。