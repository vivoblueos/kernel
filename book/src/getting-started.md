# Getting Started

We recommend you developing the kernel in Debian-12.0+ or Ubuntu-24.04+ environment to get the best tooling support.

## Prepare basic development environment
### `repo`
We are using [repo](https://source.android.com/docs/setup/reference/repo) to manage the kernel project.
Please follow https://mirrors.tuna.tsinghua.edu.cn/help/git-repo/ to install `repo`.

### `gn`
We are using [GN](https://gn.googlesource.com/gn/) to organize and build the BlueOS project, rather than
[cargo](https://doc.rust-lang.org/cargo/) the official package manager of Rust eco system. `gn` offers better
multi-language support and better build speed than `cargo`.
You can download prebuilt `gn` binaries from https://gn.googlesource.com/gn/#getting-a-binary. Put the downloaded binary
to a directory and ensure this directory is in your `${PATH}`.

### Install packages on Linux
Install packages shipped by the distro.
```bash
sudo apt install build-essential cmake ninja-build pkg-config \
                 libssl-dev gdb-multiarch curl git wget \
                 libslirp-dev python3 python3-pip meson \
                 libglib2.0-dev flex bison libfdt-dev \
                 gcc-riscv64-unknown-elf clang llvm lld \
                 python3-kconfiglib python3-tomli
```
Additionally, download and install arm toolchains
```bash
wget https://developer.arm.com/-/media/Files/downloads/gnu/14.3.rel1/binrel/arm-gnu-toolchain-14.3.rel1-x86_64-arm-none-eabi.tar.xz
tar xvf arm-gnu-toolchain-14.3.rel1-x86_64-arm-none-eabi.tar.xz -C <install-path>
wget https://developer.arm.com/-/media/Files/downloads/gnu/14.3.rel1/binrel/arm-gnu-toolchain-14.3.rel1-x86_64-aarch64-none-elf.tar.xz
tar xvf arm-gnu-toolchain-14.3.rel1-x86_64-aarch64-none-elf.tar.xz -C <install-path>
```
Add `<install-path>/arm-gnu-toolchain-14.3.rel1-x86_64-aarch64-none-elf/bin` and `<install-path>/arm-gnu-toolchain-14.3.rel1-x86_64-arm-none-eabi/bin` to your `$PATH`.

### Build and install QEMU on Linux
Download QEMU source code tarball,
```bash
wget https://download.qemu.org/qemu-10.0.2.tar.xz
tar xvf qemu-10.0.2.tar.xz
cd qemu-10.0.2
mkdir build && cd build
../configure --prefix=<install-path> --enable-slirp && \
    make -j$(nproc) install
```
Add `<install-path>/bin` to your `$PATH`.

### Install packages on macOS
```bash
brew install coreutils llvm@19 lld@19 gcc-arm-embedded cmake ninja qemu
brew tap riscv-software-src/riscv
brew install riscv-tools riscv64-elf-gcc riscv64-elf-binutils riscv64-elf-gdb
python3 -m pip install --user --break-system-packages --upgrade kconfiglib
```
For aarch64 toolchain, please refer to [arm-gnu-toolchain](https://developer.arm.com/downloads/-/arm-gnu-toolchain-downloads). It's
recommended to download tarballs rather than pkgs.
For RISC-V toolchain on macOS, please refer to [homebrew-riscv](https://github.com/riscv-software-src/homebrew-riscv?tab=readme-ov-file).

### Code formatters
We are using code formatters of corresponding programming language to keep our code style consistent. These formatters can be installed via
```bash
# On Linux
sudo apt install clang-format yapf3
```
```bash
# On macOS
brew install clang-format yapf
```

Here's the table of format command and its corresponding programming language.
| lang   | format command |
| ----   | -------------- |
| Rust   | `rustfmt`      |
| C/C++  | `clang-format` |
| Python | `yapf3`        |
| GN     | `gn format`    |

## Init and sync the project
Use following command to init the project.
```bash
mkdir blueos-dev
cd blueos-dev
```
If you have configured public ssh key on github, please use following commands
```bash
repo init -u git@github.com:vivoblueos/manifests.git -b main -m manifest.xml
```
otherwise, please try
```bash
repo init -u https://github.com/vivoblueos/manifests.git -b main -m manifest.xml
```
Then sync all repositories in the project.
```bash
repo sync
```
You might accelerate the synchronization by appending `-j$(nproc)` to the above command.
