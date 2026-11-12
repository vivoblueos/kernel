# Syscall abstraction layer

This crate provides the syscall abstraction layer for BlueKernel.

Select a mode with the GN argument `syscall_mode`:

| Mode | Calling path | Numbering |
| --- | --- | --- |
| `dsc` (default) | Direct handler calls | BlueKernel native |
| `swi` | Software interrupt | BlueKernel native |
| `linux_abi` | Software interrupt with placeholder syscall dispatch | Linux |

```sh
gn gen out/qemu_virt64_aarch64.debug.linux_abi --args='board="qemu_virt64_aarch64" build_type="debug" syscall_mode="linux_abi"'
```

Each mode selects the corresponding Rust `syscall_mode = "..."` cfg for the
header, kernel, and syscall abstraction layer. `linux_abi` is restricted to
AArch64 and RISC-V 64.
This mode currently provides Linux syscall numbering and dispatch scaffolding,
not working Linux syscall implementations or Linux binary compatibility.
The dispatcher routes `mmap`, `brk`, and `munmap` to placeholder handlers;
their implementations still use `todo!()` and panic if invoked.

`//kernel/scal:gen_linux_syscalls` generates the AArch64 and RISC-V 64 syscall
tables. `//kernel/scal:linux_syscalls` packages the selected architecture's
table into a `no_std` crate and re-exports `LinuxSysno` at the crate root for
kernel dispatch. These targets are only declared when
`syscall_mode="linux_abi"` is selected. CI builds the generator for the
supported Linux ABI board profiles.
