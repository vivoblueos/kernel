# QEMU checker

Most kernel code are tested via QEMU. We introduce QEMU checker to
assist testing the kernel.

QEMU checker must be provided with a QEMU runner script and a input
file containing check directives.  QEMU checker runs the runner script
and captures output lines of it. If output lines match conditions or
regex specified in the check directives, the checker takes
corresponding actions. Directives should be written at the header of
the input file.


directive                      | action
---                            | ---
// CHECK-FAIL: \<regex\>       | Record this line and report at exit.
// CHECK-SUCC: \<regex\>       | Record this line and report at exit.
// ASSERT-FAIL: \<regex\>      | Exit the runner and report failure.
// ASSERT-SUCC: \<regex\>      | Exit the runner and report success.
// NEWLINE-TIMEOUT: \<number\> | Timeout when checker reads the next line. Report failure if timeout occurs.
// TOTAL-TIMEOUT: \<number\>   | Total timeout for this run.

## Example
Suppose we have a kernel image for testing, named `blueos_foo_test`. 
First we have to generate a qemu runner script for it.
```gn
gen_qemu_runner("runner_for_blueos_foo_test") {
  img = ":blueos_foo_test"
  qemu = "$qemu_exe"
  board = "$board"
}
```
Then, we make a checker for the above runner.
```gn
run_qemu_checker("check_blueos_foo_test") {
  img = ":blueos_foo_test"
  runner = ":runner_for_blueos_foo_test"
  checker = "//kernel/kernel/tests/integration_test.rs"
}
```
Must be noted, the above two targets must be put in the same `BUILD.gn`.
Check directives should be put at the header of `integration_test.rs`.
```rust
// NEWLINE-TIMEOUT: 15
// ASSERT-SUCC: Kernel test end.
// ASSERT-FAIL: Backtrace in Panic.*
```

## Integrate checks in CI
CI runner only runs two toplevel targets, `default` and `check_all`.
To run check during CI, you have to put your checker target in `deps` of
`check_all` group in the toplevel `BUILD.gn`.
```gn
group("check_all") {
  deps = [ ":check_kernel" ]
}
```
