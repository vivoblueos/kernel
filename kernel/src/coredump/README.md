# Coredump Module

## Overview

Generates an ELF ET_CORE coredump on-device covering register state, memory regions, and thread information for post-mortem fault analysis.

## Triggering

Coredumps are triggered automatically through:

1. **Exception handling** — When the CPU traps a fault (SIGSEGV, SIGBUS, illegal instruction), `dump_current()` is called from the exception handler
2. **Kernel panic** — The `panic_handler` calls `dump_current()` to generate a coredump before halting
3. **Manual invocation** — Code can directly call `coredump::dump_current(&reason)` or `coredump::dump(&reason, mode)`

`dump_current()` dumps the current thread; `dump()` supports `DumpMode::Current` and `DumpMode::All`.

## Signal Mapping

Architecture-specific exception codes are mapped to POSIX signals:

| Architecture | Mapping function | Input source |
|---|---|---|
| RISC-V | `riscv_mcause_to_signo(mcause)` | mcause CSR |
| AArch64 | `aarch64_ec_to_signo(ec)` | ESR_EL1 EC field |
| Cortex-M | `arm_cfsr_to_signo(cfsr)` | CFSR (MMFSR/BFSR/UFSR) |

See the mapping tables in [signal.rs](signal.rs).

## Backend Selection (compile-time)

Backends are selected at compile time via Kconfig and `#[cfg]` chains, in priority order:

1. **`CONFIG_COREDUMP_MEM_BACKEND=y`** → MemoryBackend (static buffer)
2. **`CONFIG_ENABLE_VFS=y` and not MemoryBackend** → FileBackend (VFS file)
3. **Not MemoryBackend and not VFS** → LoggingBackend (hex-encoded serial/semihosting)

### FileBackend

Output path: `/tmp/blueos.core.<pid>` where pid is the current thread ID.

### LoggingBackend

Outputs hex-encoded ELF data line-by-line via semihosting, at most 64 hex characters per line.
Appends a trailer:
```
[BLUEOS_COREDUMP_END] mode=Current chunks=N size=NKB
```

### MemoryBackend

Writes the coredump to a static kernel buffer (`COREDUMP_STORAGE`) placed in the `.coredump_bss` linker section, which is excluded from BSS memory region collection. Sets `COREDUMP_VALID` after completion.

## Kconfig Options

| Option | Type | Default | Description |
|---|---|---|---|
| `ENABLE_COREDUMP` | bool | n | Global coredump switch |
| `COREDUMP_MEM_BACKEND` | bool | n | Use MemoryBackend (depends on ENABLE_COREDUMP) |
| `COREDUMP_BUF_SIZE` | int | 64KB (Cortex-M) / 256KB (32-bit) / 4MB | ELF buffer size in bytes |

Default values:
- Cortex-M (resource-constrained): 64KB
- Other 32-bit platforms: 256KB
- 64-bit platforms: 4MB

## Integration Test

```bash
# Run the coredump integration test
ninja -C out/qemu_riscv64.debug.swi run_coredump_test
```

The test constructs a synthetic `CoredumpReason { signo: 6, code: 0, fault_addr: 0, arch_specific: 0 }`,
calls `dump_current()`, and verifies successful output.

Test assertions are defined in [tests/coredump.checker](../tests/coredump.checker):
```
// ASSERT-SUCC: Coredump integration test end.
// ASSERT-FAIL: Backtrace in Panic.*
```

## Serial Log Parser Tool

When using LoggingBackend, coredump data is output as hex-encoded text over serial/semihosting. Use the parser tool to reassemble it into a `.core` ELF file:

```bash
# Parse from QEMU serial log
python3 tools/coredump_parser.py < qemu_log.txt -o blueos.core

# Specify input file
python3 tools/coredump_parser.py --input qemu_log.txt -o blueos.core

# Validate the generated core file
python3 tools/coredump_parser.py --input qemu_log.txt -o blueos.core --validate

# Verbose output
python3 tools/coredump_parser.py --input qemu_log.txt -o blueos.core --verbose
```

Options:
- `--input` / `-i`: Input file (default stdin)
- `--output` / `-o`: Output core file path
- `--validate`: Run `readelf` to validate the generated core file
- `--verbose`: Print metadata and size information

## Architecture Support

| Architecture | Status | Boards |
|---|---|---|
| RISC-V 64 | Supported | qemu_riscv64 |
| RISC-V 32 | Supported | qemu_riscv32, gd32vw553_eval |
| AArch64 | Supported | qemu_virt64_aarch64 |
| Cortex-M | Supported | qemu_mps2_an385 |
| ESP32-C3 | Supported | seeed_xiao_esp32c3 (RISC-V 32) |

## Notes

1. **Buffer size**: `COREDUMP_BUF_SIZE` must be large enough to hold the complete ELF output, or `write()` will return an error.
2. **Re-entrancy**: `COREDUMP_IN_PROGRESS` prevents recursive coredump triggers.
3. **Interrupt state**: Coredump executes with interrupts disabled (guaranteed by the exception handler).
4. **`.coredump_bss` section**: The ELF buffer and MemoryBackend storage are placed in this section so that BSS memory dumps do not include the buffers themselves.