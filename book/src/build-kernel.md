# Build kernel image

The kernel currently supports multiple boards.

- qemu_mps2_an385
- qemu_mps3_an547
- qemu_virt64_aarch64
- qemu_riscv64

To build a kernel image for specified board, like `qemu_mps2_an385`, use command
```
gn gen out/qemu_mps2_an385.release/ --args='build_type="release" board="qemu_mps2_an385"'
ninja -C out/qemu_mps2_an385.release
```
To run tests, type
```
ninja -C out/qemu_mps2_an385.release check_all
```

## Args and their semantics.
| arg        | semantics |
| ---        | ---       |
| build_type | Configuration for the build |
| board      | Name of the board targeted to |
