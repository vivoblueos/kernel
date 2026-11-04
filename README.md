# BlueKernel POSIX 兼容层

[BlueKernel](https://github.com/vivoblueos/kernel) 的 POSIX 补全分支。目标 **POSIX.1-2024（Issue 8）**，做法是「补接口 + 补承载语义的内核能力」——地址空间、特权级、进程模型、uaccess。

上游自述（`kernel/README*.md`）与书稿（`book/`）基本保持原样；书稿只删除了多仓同步说明（本项目已改为单仓库维护，DF-13 已收口）。根目录只有两份文档：本文件讲**项目现状与结构**，[`DEFECTS.md`](DEFECTS.md) 讲**缺陷与路线**。

> **本文件职责**：定位、能力边界、状态数字、板级验证深度、代码地图、构建方式、约定。缺陷正文只在 `DEFECTS.md` 出现一次。

---

## 1. 能做什么 / 不能做什么

| 能 | 依据 |
| --- | --- |
| rv64 上跑多进程用户态：EL0 + 每进程 Sv39 页表 + W^X + 按需分页 + COW | `apps/user/proc` 端到端 |
| `fork` / `execve` / `waitpid` / `exit_group` / `getpid` / `getppid` 全链路 | EL0 smoke：父进程 `waitpid` 取回 7 |
| 85 个 syscall 声明与分发，其中 84 个真实现 | `tools/posix_audit.py` |
| 12 块板 + host 目标全部保留编译 | `build/boards/` |
| Issue 8 required 导出 37 / 75 | `report/posix_baseline.json` |

| 不能 | 编号 |
| --- | --- |
| 跑 busybox ash（仍缺 `socketpair`/`epoll`/`mkfifo`） | DF-04 |
| 在 aarch64 / riscv32 跑用户态（EL0 向量直接 panic） | DF-06 |
| 内核自身有特权级兜底（内核仍跑 M 态） | DF-05 |
| 动态链接（只有 PIE 自重定位，无 `PT_INTERP`/符号解析/`dlopen`） | DF-21 |
| 宣称 Issue 8 conformance（37/75，且 2 项本仓未实现） | DF-19 |
| 离线构建（缺 `external/`，构建文件 204 处静态引用） | DF-12 |

**「目标」不等于「达标」。** 本分支不宣称 conformance，只宣称这一轨做到了哪里。

---

## 2. 状态

2026-11-03，分支 `posix-issue8-phase0`。数字均可用右列命令复核。

| 指标 | 数值 | 复核 |
| --- | --- | --- |
| 内核 `kernel/kernel/src` / `librs/src` | 63.4k / 20.2k 行 Rust | `find <dir> -name '*.rs' \| xargs wc -l` |
| syscall 声明 / 分发 / 真实现 | 85 / 85 / 84 | `python3 tools/posix_audit.py` |
| Issue 8 required 已导出 | 37 / 75（49.3%） | 同上 `issue8.summary` |
| POSIX 用例 | 76 passed / 0 failed / known-fail=1 / skipped=1，另 U 态探针 32 条 | `ninja -C out/qemu_riscv64.debug run_posix_cases` |
| 用户态 | rv64 多进程 + U 态建线程跑通 | `ninja -C out/qemu_riscv64.debug run_shell_smoke` |
| 缺陷 | 14 项未完成（P1 8 / P2 4 / P3 2），已收口 7 项归档 | `python3 tools/doc_index_check.py` |

两处读表须知：

- 唯一非 `real` 的是 `Nop`：handler 按定义返回 0，`stub` 是永久标签，不是待办。
- **用例数与基线差 1** 是审计器的计数 bug（正则漏检 `POSIX_CASE_XFAIL`），不是口径差异。修好前以 `run_posix_cases` 输出为准（DF-14）。

Issue 8 的 75 项 required 里，37 项由 librs 导出；剩余 38 项 = 28 项编译器内建（`<stdatomic.h>`）+ 8 项 newlib 4.4.0 提供（`memmem`/`strlcpy`/`strlcat`/`qsort_r`/`at_quick_exit`/`quick_exit`/`wcslcpy`/`wcslcat`）+ **2 项本仓仍未实现（`sig2str`/`str2sig`）**。37/75 是本仓职责那一轨的完成度，不是 Issue 8 的完成度。

---

## 3. 板级支持

12 块板 + 1 个 host 目标，与上游一致（`build/boards/*.gni` 与 `kernel/kconfig/config/` 一一对应）。

| 板 | 架构 | 验到哪一步 |
| --- | --- | --- |
| `qemu_riscv64` | RV64 / Sv39 | 用例层：`check_all` + 76 条 POSIX 用例 + U 态 smoke |
| `qemu_virt64_aarch64` | AArch64 / EL1 | 用例层：`check_all` + 76 条用例（**无 U 态**，DF-06） |
| `qemu_riscv32` | RV32 | `check_all`（该板无 POSIX 用例目标） |
| `qemu_mps2_an385` | Cortex-M3 | 从零构建 + `check_all`（`thread_metric` flaky，DF-15） |
| `qemu_mps3_an547`、`gd32e507_eval`、`gd32vw553_eval` | Cortex-M55 / M33、Nuclei RV32 | 仅编译链接 |
| `raspberry_pico2_cortexm`、`seeed_xiao_esp32c3`、`esp32c6_devkitc_1` | RP2350、ESP32-C3/C6 | 仅编译链接 |
| `rk3568` | Cortex-A55 ×4 | 仅编译链接（无硬件） |
| `newlib_mps3_an547` | Cortex-M55 + newlib | **本轮未跑** |
| `none` | x86_64 host | `check_all` |

**「保留 12 板」= 保留编译能力，不等于全部可运行。** 只有 rv64 与 aarch64 验到用例层；「仅编译链接」不代表上板可用。

Cortex-M 与 ESP32 全系无 MMU：`user` 模块整体编掉（`#[cfg(target_arch = "riscv64")]`），进程类 syscall 编成 `ENOSYS`，`in_user_space()` 恒 `false`。同一套源码按目标裁掉它承载不了的语义。

---

## 4. 与上游的差异

对照 `vivoblueos/kernel` `main`（2026-11-03 快照）。

| 维度 | 上游 | 本分支 |
| --- | --- | --- |
| 特权级 | rv64 仅 M 态（`arch/riscv/mod.rs:41` 自述尚未支持 S/U 态，全文 0 次 `satp`）；aarch64 从 EL2 落到 EL1 常驻 | 增加 U 态应用 + PMP + Sv39；内核仍 M 态（DF-05） |
| 地址空间 | 无分页概念 | 每进程 Sv39 根页表、ELF 按段映射、按需分页、COW、W^X |
| 进程模型 | 只有线程容器 | `fork`/`execve`/`waitpid` + 僵尸语义 |
| syscall | 71 | 85（追加式编号，前 71 个编号不动） |
| `kernel/kernel/src` | 210 个 `.rs` / 1.79 MB | 223 个 / 2.12 MB（**+19%**） |
| 新增模块 | — | `arch/riscv/{mmu,pmp,sbi}.rs`、`kernel/elf.rs`、`kernel/user/`、`vfs/uptr.rs`、`signal/delivery.rs` |
| 板卡 | 12 + `none` | 一致 |
| CI | 包根 `.github/` 有 | 包根无 CI（DF-11）；子仓子树同步流水线已移除，改为单仓库维护 |
| 文档侧重 | README + book | 同上，另加本文件与 `DEFECTS.md` |

**取舍**：换来隔离与 POSIX 进程语义，付出内核 +19% 体积与 M 态结构债（DF-05）。安全态势从「无边界」变成「有边界但边界未压实」——PMP 仍是 4 GiB 单窗（DF-07），`ioctl` 参数未定型（DF-08）。

---

## 5. 代码结构

### 5.1 顶层

| 目录 / 文件 | 角色 |
| --- | --- |
| `kernel/` | 内核主体：`kernel/kernel` 是本体，另有 `arch`/`allocator`/`hal`/`driver`/`loader`/`rsrt` 等子 crate |
| `libc/` | 上游 `rust-lang/libc` 的 fork：只提供类型、常量与函数**声明** |
| `librs/` | libc 实现：POSIX 语义层 + C 符号导出（`printf`/`open`/`pthread_*`） |
| `apps/` | 用户态：`shell`/`example`/`bench`，`user/` 下是 `hello`、`proc`、`posix_u` 三个 EL0 程序 |
| `build/` | GN/Ninja 配置、12 块板定义、toolchain |
| `tools/` | `bk.sh`（单入口）、`posix_audit.py`（四层覆盖度）、`doc_index_check.py`、`smode_probe/`（S 态探针）、`kernel_lang_gate.py` |
| `report/` | 度量 JSON：`posix_baseline.json`（**门禁基准**）、`posix_coverage.json`（**陈旧快照**，DF-18）、`baseline.json`、`kernel_lang.json` |
| `book/` | mdBook 开发手册（上游同步，不修改） |

### 5.2 内核源码地图（`kernel/kernel/src/`）

| 路径 | 职责 |
| --- | --- |
| `arch/riscv/mmu.rs` | Sv39 页表：walk / 映射 / 权限 / `satp` |
| `arch/riscv/pmp.rs` | 每 hart 的 PMP 窗口 |
| `arch/riscv/sbi.rs` | SBI 客户端 + 服务端 + 寄存器编解码（Phase 0） |
| `arch/riscv/firmware.rs` | M 态固件侧实现（**规划中**，随 DF-05 Phase 1+2 落地） |
| `arch/riscv/trap.rs` | 陷阱入口、用户缺页与故障分派 |
| `arch/aarch64/` | EL2 → EL1 入口、异常向量（EL0 未支持，DF-06） |
| `user/mod.rs` | `AddressSpace`、`spawn`/`exec`/`fork`、`waitpid`、`mmap` |
| `vfs/uptr.rs` | `copy_from_user` 族——唯一允许碰用户指针的地方 |
| `process/` | 进程表、僵尸与回收 |
| `signal/` | 默认动作表、`delivery.rs`、POSIX 定时信号 |
| `header/src/lib.rs` | `NR` 枚举（syscall 号唯一来源） |
| `boot.rs` / `config.rs` / `lib.rs` | 启动、配置、crate 入口 |
| `arch/`、`boards/`、`thread/`、`scheduler/`、`vfs/`、`mm/`、`net/`、`drivers/`、`devices/` | 架构层、板级、线程、调度、文件系统、内存、网络、驱动 |

### 5.3 打包范围

包含：`kernel/` `libc/` `librs/` `apps/` `build/` `tools/` `report/` `book/`、根配置 `.gn` 与 `BUILD.gn`、本文件与 `DEFECTS.md`。

不含：`out/`（构建产物）、`.git/`（版本历史）、`external/`（vendored 依赖，约 328 MB）。

**`external/` 需要自行从上游获取**：它是上游 [`vivoblueos/kernel`](https://github.com/vivoblueos/kernel) 的快照内容（`external/vendor/` 及 `quickjs`、`quickjs-ng`、`CMSIS*`、`nuclei-sdk`、`gnrt` 等）。取同版本的上游树，把其中的 `external/` 整个目录复制到本项目根目录即可：

```bash
git clone --depth 1 https://github.com/vivoblueos/kernel.git /tmp/bluekernel-upstream
cp -a /tmp/bluekernel-upstream/external ./external
```

构建文件有 204 处 `//external/...` 静态引用，缺它连 `gn gen` 都过不去（见 DF-12）；补齐后即可离线构建。

---

## 6. 构建与验证

依赖 Docker 与 `ghcr.io/vivoblueos/kernel:latest`：

```bash
# 构建 + 全量检查（check_all = adapter + kernel + loader + rsrt + librs + 3×clippy + run_posix_cases）
docker run --rm -v "$PWD:/work" -w /work ghcr.io/vivoblueos/kernel:latest \
  bash -lc 'BK_BOARD=qemu_riscv64 BK_IN_CONTAINER=1 tools/bk.sh test'

# 只跑 POSIX 用例
docker run --rm -v "$PWD:/work" -w /work ghcr.io/vivoblueos/kernel:latest \
  bash -lc 'ninja -C out/qemu_riscv64.debug run_posix_cases'

# 用户态 smoke（应看到 hello from user mode + proc smoke exited with 0）
ninja -C out/qemu_riscv64.debug run_shell_smoke

# 覆盖度 / 文档一致性
python3 tools/posix_audit.py --check report/posix_baseline.json
python3 tools/doc_index_check.py
```

换板只改 `BK_BOARD`。`tools/bk.sh build` 只建库不建镜像；`bin/` 里的 ELF 由 `check_all` 或 `ninja <out>/bin/shell` 产出。构建细节、加 syscall 流程、QEMU checker 见 `book/src/`。

不在 `tools/ci/run_profile.py` 列表里的两块板（`esp32c6_devkitc_1`、`newlib_mps3_an547`）直接调 GN：

```bash
gn gen out/esp32c6_devkitc_1.debug --args='board="esp32c6_devkitc_1" build_type="debug"'
ninja -C out/esp32c6_devkitc_1.debug default
```

---

## 7. 约定

- **Rust 优先**。内核里 C/汇编只允许出现在无法用 Rust 表达的位置（启动入口、异常向量）；`tools/kernel_lang_gate.py` 是门禁（372 个 `.rs`，0 违规）。
- **用户指针必须走 uaccess**（`vfs/uptr.rs`），禁止 `unsafe { *ptr }` 直解引用。
- **新 syscall 三处登记**：`NR` 枚举、`syscall_table!` 分发、librs 的 C 包装，并补 C 用例。**新调用追加在枚举尾部**，前面的编号是 ABI。
- **`check_all` 全绿才提交**；POSIX 基线不得倒退。
- **缺陷只写 `DEFECTS.md`**：本文件只引用 `DF-xx` 编号，不复制正文。同一事实分头维护是 DF-16 的成因。
- **状态口径**：任何跨架构结论必须写明目标架构。默认语境是 rv64；aarch64 与 riscv32 没有用户态。
- **单仓库维护**：不再与上游子树同步；改动保留在本地分支，按阶段提交。
- **只维护这两份根文档**：`kernel/README*.md` 与 `book/` 是上游同步内容，不修改。

## 许可证

与上游一致（Apache-2.0）。
