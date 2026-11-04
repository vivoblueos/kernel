# Add a new syscall

Adding a new syscall in the kernel is easy.

There are 3 steps.

1. Add new syscall number for the new syscall in `header/src/lib.rs`.
```rust
pub enum NR {
    Read,
}
```

2. Implement the new syscall in `kernel/src/syscall_handlers/mod.rs`.

This is generally done via `define_syscall_handler!` if the syscall is trivial. For example
```rust
define_syscall_handler!(
read(fd: i32, buf: *mut i8, len: usize) -> c_long {
    // Implement your vfs read.
});
```

3. Register the new syscall in `kernel/src/syscall_handlers/mod.rs`.

Add a new entry in `syscall_table!`. For example,
```rust
(Read, read),
```
Must be noted, the first operand **MUST** be the unqualified name of the `NR` enumeration.
