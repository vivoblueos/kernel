# Run Coverage

We generate the code needed for coverage statistics by adding `-Cinstrument-coverage` during compilation, and generate coverage data through the integration of [minicov](https://crates.io/crates/minicov) and [semihosting](https://crates.io/crates/semihosting). Finally, we use the [grcov](https://crates.io/crates/grcov) tool to generate readable coverage data in HTML format. All of these have been integrated into our build system, and coverage data can be generated using the following commands：

```bash
gn gen out/qemu_riscv64.cov/ --args='build_type="coverage" board="qemu_riscv64"'
ninja -C out/qemu_riscv64.cov check_coverage
```

If you get a prompt that grcov is not found, you can install it via 
```bash
cargo install grcov
```

After building and running, you can find merged coverage report in the
`./out/qemu_riscv64.cov/cov_report` directory. Open the `index.html`
file in the directory to view the coverage data.
