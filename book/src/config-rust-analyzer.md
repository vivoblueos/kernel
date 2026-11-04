# Use rust-analyzer in VSCode

We recommend you to use rust-analyzer extension in VSCode to support development of BlueOS kernel.

However, since we are using `gn`, rather than `Cargo.toml`, to manage our project, the rust-analyzer extension in VSCode might not work
out-of-box. You should use following commands[^1] to get the extension work
```shell
gn gen out/qemu_mps2_an385 --export-rust-project
ln -sfn out/qemu_mps2_an385/rust-project.json
```
[^1]: https://chromium.googlesource.com/chromium/src/+/refs/heads/main/docs/rust.md#using-vscode
