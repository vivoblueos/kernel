FROM ubuntu:24.04

# Set environment variables
ENV DEBIAN_FRONTEND=noninteractive
ENV PATH="/opt/sysroot/usr/local/bin:/opt/sysroot/usr/local/lib/rustlib/x86_64-unknown-linux-gnu/bin:/opt/arm-gnu-toolchain-14.2.rel1-x86_64-arm-none-eabi/bin/:/opt/arm-gnu-toolchain-14.2.rel1-x86_64-aarch64-none-elf/bin/:${PATH}"

# Install system packages
RUN apt-get update && \
    apt-get install -y \
        git \
        clang \
        python3-kconfiglib \
        ninja-build \
        generate-ninja \
        curl \
        libfdt-dev \
        libslirp-dev \
        libglib2.0-dev \
        build-essential \
        pkg-config \
        && rm -rf /var/lib/apt/lists/*

# Install Arm GNU toolchain (ARM Cortex-M)
RUN curl -L -o arm-toolchain.tar.xz https://developer.arm.com/-/media/Files/downloads/gnu/14.2.rel1/binrel/arm-gnu-toolchain-14.2.rel1-x86_64-arm-none-eabi.tar.xz && \
    tar xf arm-toolchain.tar.xz -C /opt && \
    rm arm-toolchain.tar.xz

# Install Arm64 GNU toolchain (AArch64)
RUN curl -L -o aarch64-toolchain.tar.xz https://developer.arm.com/-/media/Files/downloads/gnu/14.2.rel1/binrel/arm-gnu-toolchain-14.2.rel1-x86_64-aarch64-none-elf.tar.xz && \
    tar xf aarch64-toolchain.tar.xz -C /opt && \
    rm aarch64-toolchain.tar.xz

# Download and unpack prebuilt QEMU
RUN mkdir -p /opt/sysroot && \
    curl -L -o qemu.tar.xz https://github.com/vivoblueos/toolchain/releases/download/v0.8.0/qemu-2025_08_05_12_17.tar.xz && \
    tar xf qemu.tar.xz -C /opt/sysroot && \
    rm qemu.tar.xz

# Download and unpack prebuilt Rust toolchain
RUN curl -L -o blueos-toolchain.tar.xz https://github.com/vivoblueos/toolchain/releases/download/v0.8.0/blueos-toolchain-ubuntu-latest-2025_09_16_08_50.tar.xz && \
    tar xf blueos-toolchain.tar.xz -C /opt/sysroot && \
    rm blueos-toolchain.tar.xz

# Install bindgen and cbindgen
RUN cargo install bindgen-cli@0.72.1 cbindgen@0.29.0

# Install repo
RUN curl -L -o /opt/sysroot/usr/local/bin/repo https://storage.googleapis.com/git-repo-downloads/repo && \
    chmod a+x /opt/sysroot/usr/local/bin/repo

# Set working directory
WORKDIR /blueos-dev

CMD ["/bin/bash"]