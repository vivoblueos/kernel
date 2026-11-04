# Building the Rust toolchain for BlueOS kernel

We have forked upstream [Rust compiler](https://github.com/rust-lang/rust.git) to support BlueOS kernel
targeted to `*-vivo-blueos-*` and BlueOS kernel's Rust-std.

We'll finally contribute our changes to the upstream repository and make `*-vivo-blueos-*`
a [tier](https://doc.rust-lang.org/rustc/target-tier-policy.html) Rust target.

## Clone the downstream repository
Run
If you have configured public ssh key on github, please use following commands,

```bash
git clone git@github.com:vivoblueos/rust.git  
git clone git@github.com:vivoblueos/cc-rs.git  
git clone git@github.com:vivoblueos/libc.git
```  
otherwise, please try
```bash
git clone https://github.com/vivoblueos/rust.git  
git clone https://github.com/vivoblueos/cc-rs.git  
git clone https://github.com/vivoblueos/libc.git 
```
The `blueos-dev` branch is set as default, so no manual branch switching is required.

## Setup Rust mirror site
In China, we recommend you to use mirror site for `crates.io` and `rustup`. Add following lines to your `~/.bashrc`
```bash
export RUSTUP_DIST_SERVER=https://mirrors.ustc.edu.cn/rust-static
export RUSTUP_UPDATE_ROOT=https://mirrors.ustc.edu.cn/rust-static/rustup
```
and then type
```bash
source ~/.bashrc
```

## Install via `x` script
Run the following commands in your bash shell. These instructions work for both Linux and macOS platforms:
```bash
export CARGO_NET_GIT_FETCH_WITH_CLI=true
export DESTDIR=<choose-your-install-prefix>
cd rust
cp config.blueos.toml config.toml
./x.py install -i --stage 1 compiler/rustc
./x.py install -i --stage 1 library/std --target aarch64-vivo-blueos-newlib
./x.py install -i --stage 1 library/std --target thumbv7m-vivo-blueos-newlibeabi
./x.py install -i --stage 1 library/std --target thumbv8m.main-vivo-blueos-newlibeabihf
./x.py install -i --stage 1 library/std --target riscv64-vivo-blueos
./x.py install -i --stage 1 library/std --target riscv32-vivo-blueos
./x.py install -i --stage 1 library/std --target riscv32imc-vivo-blueos
./x.py install -i --stage 0 rustfmt
./x.py install -i --stage 0 rust-analyzer
./x.py install -i --stage 0 clippy
```

You must also install the host machine's standard library and LLVM tools.

For Linux:
```bash
./x.py install -i --stage 1 library/std --target x86_64-unknown-linux-gnu
cp -rav build/x86_64-unknown-linux-gnu/llvm/{bin,lib} ${DESTDIR}/usr/local
```

For macOS:
```bash
./x.py install -i --stage 1 library/std --target aarch64-apple-darwin
cp -av build/aarch64-apple-darwin/llvm/{bin,lib} ${DESTDIR}/usr/local
```

To use the kernel toolchain, add the following to your environment:
```bash
export PATH=${DESTDIR}/usr/local/bin:${PATH}
```

Or if you want to manage the blueos toolchain using rustup, you can try:
```bash
ln -s ${DESTDIR}/usr/local ~/.rustup/toolchains/blueos-dev
rustup default blueos-dev
```
