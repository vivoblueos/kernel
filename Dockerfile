FROM ubuntu:24.04

# Set environment variables
ENV DEBIAN_FRONTEND=noninteractive
ENV PATH="/opt/sysroot/usr/local/bin:/opt/sysroot/usr/local/lib/rustlib/x86_64-unknown-linux-gnu/bin:/opt/arm-gnu-toolchain-14.2.rel1-x86_64-arm-none-eabi/bin/:/opt/arm-gnu-toolchain-14.2.rel1-x86_64-aarch64-none-elf/bin/:/opt/xpack-riscv-none-elf-gcc-14.2.0-3/bin/:/opt/skywalking-license-eye-0.7.0-bin/bin/linux/:${PATH}"

# Install system packages
RUN apt-get update \
    && apt-get install -y \
        git \
        clang lld \
        python3-kconfiglib \
        python3-pip \
        ninja-build \
        generate-ninja \
        curl \
        libfdt-dev \
        libslirp-dev \
        libglib2.0-dev \
        build-essential \
        pkg-config \
        clang-format yapf3 npm \
        libpixman-1-0 \
        libsdl2-dev \
    && rm -rf /var/lib/apt/lists/*
RUN pip3 install esptool==4.7.0 --break-system-packages

# Install Arm GNU toolchain (ARM Cortex-M)
RUN curl -L -o arm-toolchain.tar.xz https://developer.arm.com/-/media/Files/downloads/gnu/14.2.rel1/binrel/arm-gnu-toolchain-14.2.rel1-x86_64-arm-none-eabi.tar.xz \
    && tar xf arm-toolchain.tar.xz -C /opt \
    && rm arm-toolchain.tar.xz

# Install Arm64 GNU toolchain (AArch64)
RUN curl -L -o aarch64-toolchain.tar.xz https://developer.arm.com/-/media/Files/downloads/gnu/14.2.rel1/binrel/arm-gnu-toolchain-14.2.rel1-x86_64-aarch64-none-elf.tar.xz \
    && tar xf aarch64-toolchain.tar.xz -C /opt \
    && rm aarch64-toolchain.tar.xz

# Install RISCV32 GNU toolchain (RISCV32)
RUN curl -L -o riscv32-toolchain.tar.gz https://github.com/xpack-dev-tools/riscv-none-elf-gcc-xpack/releases/download/v14.2.0-3/xpack-riscv-none-elf-gcc-14.2.0-3-linux-x64.tar.gz \
    && tar xf riscv32-toolchain.tar.gz -C /opt \
    && rm riscv32-toolchain.tar.gz

# Download and unpack prebuilt QEMU
RUN mkdir -p /opt/sysroot \
    && curl -L -o qemu.tar.xz https://github.com/vivoblueos/toolchain/releases/download/v0.8.0/qemu-2025_08_05_12_17.tar.xz \
    && tar xf qemu.tar.xz -C /opt/sysroot \
    && rm qemu.tar.xz

# Download and unpack prebuilt Rust toolchain
RUN curl -L -o blueos-toolchain.tar.xz https://github.com/vivoblueos/toolchain/releases/download/v0.8.0/blueos-toolchain-ubuntu-latest-2025_10_21_09_53.tar.xz \
    && tar xf blueos-toolchain.tar.xz -C /opt/sysroot \
    && rm blueos-toolchain.tar.xz

# Install repo
RUN curl -L -o /opt/sysroot/usr/local/bin/repo https://storage.googleapis.com/git-repo-downloads/repo \
    && chmod a+x /opt/sysroot/usr/local/bin/repo

# Install license-eye
RUN curl -L -o skywalking-license-eye.tgz https://github.com/apache/skywalking-eyes/releases/download/v0.7.0/skywalking-license-eye-0.7.0-bin.tgz \
    && tar xf skywalking-license-eye.tgz -C /opt \
    && rm skywalking-license-eye.tgz

# Install yamlfmt
RUN curl -L -o yamlfmt.tar.gz https://github.com/google/yamlfmt/releases/download/v0.18.0/yamlfmt_0.18.0_Linux_x86_64.tar.gz \
    && tar xf yamlfmt.tar.gz -C /opt/sysroot/usr/local/bin/ \
    && chmod a+x /opt/sysroot/usr/local/bin/yamlfmt \
    && rm yamlfmt.tar.gz

# Install esp32 QEMU.
RUN curl -L -o qemu-riscv32-softmmu-esp_develop_9.2.2_20250817-x86_64-linux-gnu.tar.xz https://github.com/espressif/qemu/releases/download/esp-develop-9.2.2-20250817/qemu-riscv32-softmmu-esp_develop_9.2.2_20250817-x86_64-linux-gnu.tar.xz \
    && tar -xvf qemu-riscv32-softmmu-esp_develop_9.2.2_20250817-x86_64-linux-gnu.tar.xz -C /opt \
    && rm qemu-riscv32-softmmu-esp_develop_9.2.2_20250817-x86_64-linux-gnu.tar.xz
RUN mkdir -p /opt/qemu
RUN curl -L -o esp32-qemu.tar.xz https://github.com/vivoblueos/toolchain/releases/download/v0.8.0/esp32-qemu-2026_04_02_03_47.tar.xz \
    && tar xf esp32-qemu.tar.xz -C /opt/qemu \
    && rm esp32-qemu.tar.xz
WORKDIR /opt/qemu/usr/local/bin
RUN mv qemu-system-riscv32 qemu-esp32-riscv32
ENV PATH="/opt/qemu/usr/local/bin:${PATH}"

# Install bindgen and cbindgen to /opt/sysroot/usr/local/bin
RUN CARGO_INSTALL_ROOT=/opt/sysroot/usr/local cargo install bindgen-cli@0.72.1 --locked \
    && curl -L -o cbindgen https://github.com/mozilla/cbindgen/releases/download/0.29.0/cbindgen-ubuntu22.04 \
    && chmod a+x cbindgen \
    && mv cbindgen /opt/sysroot/usr/local/bin

# Set working directory
WORKDIR /blueos-dev

CMD ["/bin/bash"]