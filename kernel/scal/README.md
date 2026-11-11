# Syscall abstraction layer

This crate provides the syscall abstraction layer for BlueKernel.

Select a mode with the GN argument `syscall_mode`:

| Mode | Calling path | Numbering |
| --- | --- | --- |
| `dsc` (default) | Direct handler calls | BlueKernel native |
| `swi` | Software interrupt | BlueKernel native |
| `linux_abi` | Reserved for Linux ABI support | Linux, integration pending |

```sh
gn gen out/qemu_virt64_aarch64.debug.linux_abi --args='board="qemu_virt64_aarch64" build_type="debug" syscall_mode="linux_abi"'
```

Each mode selects the corresponding Rust `syscall_mode = "..."` cfg for the
header, kernel, and syscall abstraction layer. `linux_abi` is restricted to
AArch64 and RISC-V 64.
Linux syscall numbering and dispatch are not connected yet; selecting this
mode does not provide Linux syscall compatibility. In this mode,
`//kernel/scal:gen_linux_syscalls` generates the AArch64 and RISC-V 64 syscall
tables and is built with `blueos_scal`. The target is only declared when
`syscall_mode="linux_abi"` is selected. CI builds this generator for the
supported Linux ABI board profiles.
