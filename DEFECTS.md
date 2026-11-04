# 缺陷与实施计划

> 分支 `posix-issue8-phase0` · 2026-11-04
> **本文件职责**：未完成缺陷与实施计划的唯一来源。根目录只有两份文档：[`README.md`](README.md) 讲现状与结构，本文件讲缺陷与路线；README 只引用编号，不复制正文。
> 每条缺陷给 **证据**（`文件:行` 或可复核命令）、**影响**、**完成判据**。判据不能量化的条目不入册。
> 已收口条目只保留归档表，不再占用正文；编号不复用。

## 归档（已收口，不再展开）

| 编号 | 结论 |
| --- | --- |
| DF-01 | `pthread_sigmask` 已导出，`run_posix_cases` 通过。 |
| DF-02 | 同步故障与异步信号统一经栈上 `sigframe` + trampoline `sigreturn`，U 态 handler 可返回。 |
| DF-03 | `fork` 用 `fd_manager().fork_copy()` 复制槽位，共享 `File`（offset 共享）。 |
| DF-04（部分） | `pipe`/`dup`/`dup2`/`F_DUPFD`/`select` 与 termios uaccess 已落地并有 EL0 用例；剩余项并入 DF-04 正文。 |
| DF-16 | 文档口径统一为「EL2 起始、EL1 常驻、无 EL0」，缺陷只写本文件。 |
| DF-20 | `uname` 填真实字段；不可实现的调用统一 `ENOSYS`；返回值诚实性由用例覆盖。 |
| DF-13 | 已删除 josh 子树同步工具（`tools/josh/`、各仓 `josh-sync.toml`）与 `bluekernel-{pull,push}`、`cross_repos_build` 流水线，改为单仓库维护。 |

## 严重度与当前存量

| 级别 | 含义 | 条数 | 编号 |
| --- | --- | --- | --- |
| **P0 阻断** | C 程序无法链接/运行，或 POSIX 语义错到程序行为不对 | 0 | — |
| **P1 结构** | 不是 bug，是架构边界；修它要改特权级 / 页表 / ABI | 8 | DF-05–DF-10、DF-17、DF-21 |
| **P2 工程** | 构建、CI、同步流程上的债 | 4 | DF-11、DF-12、DF-14、DF-15 |
| **P3 文档度量** | 口径不一致、度量失真、门禁漏检 | 2 | DF-18、DF-19 |

---

# 第一部分 · 未完成缺陷

## P1 · 结构

### DF-05 内核跑在 M 态：无兜底、不虚拟化、uaccess 必须显式拷贝

- **证据**：`arch/riscv/mod.rs` 的 `arch_bootstrap!` 直接进 M 态 `bootstrap()`；`enter_user` 用 `mret` + `MPP=U`；rv64 上 `satp` 对 M 态不生效。
- **影响**：① 内核是芯片上最高特权，写坏 `PMP`/`satp`/`mstatus` 后没有一层能接管或复位；② 内核跑物理地址，无 KPTI、无内核 ASLR；③ 用户指针必须经 bounce buffer 拷贝（DF-09）。
- **判据**：附录 A 的四条验收全绿。
- **现状**：Phase 0（`tools/smode_probe/`）已实测通过；Phase 1+2 未开工。实施步骤见附录 A。

### DF-06 用户态只在 rv64 成立，aarch64 的 EL0 直接 panic

- **证据**：`lib.rs` — `#[cfg(target_arch = "riscv64")] pub mod user;`；`arch/aarch64/vector.rs` 四个 EL0 向量全部指向 `el0_not_supported`；内核从 EL2 落到 EL1 后常驻。
- **影响**：**「支持 ARM64」当前只到「EL1 内核能跑」**。进程类 syscall 在 aarch64/riscv32 编成 `ENOSYS`，`in_user_space()` 恒 `false`。跨架构的 POSIX 结论必须限定为「rv64 结论」。
- **判据**：aarch64 跑通同一个 `proc` smoke。

### DF-07 PMP 是低 4 GiB 单窗、全权限、不锁定

- **证据**：`arch/riscv/pmp.rs` — `CFG_RWX_NAPOT = 0b0001_1111`、`PMPADDR0_NAPOT_4GIB = 0x1fff_ffff`，即一条 `2^32` 字节的 `R`/`W`/`X` NAPOT 条目，`L=0`。
- **影响**：U 态**物理**可达范围是整片低 4 GiB，只有页表兜虚拟面。页表若出错（或 `satp` 被写坏），物理面没有第二道闸。演示够用，安全评审过不去。
- **为什么这么写**：`L=0` 必须如此（锁定条目会连带约束 M 态且不可解锁）；4 GiB 同时覆盖 QEMU `virt` 的 RAM 与镜像基址，且不要求早期启动知道平台内存图。
- **判据**：窗口收紧到板级真实 RAM 区间，越界访问触发 access fault。与附录 A 的 Phase 3 同批做。

### DF-08 `ioctl` 的 `arg` 仍是裸 `usize`

- **证据**：`vfs/uptr.rs` 模块头「What is *not* covered」——`arg` 由各驱动自行解释，`request` 决定它是整数、指针还是结构体。`framebuffer` 的四个用户指针仍是裸解引用。
- **影响**：每新增一个驱动的 ioctl 就多一个绕过 uaccess 的入口。当前唯一使用者是终端。
- **判据**：按 `request` 分类的参数类型表；所有用户指针型 ioctl 走 uaccess；非法指针返回 `EFAULT` 且日志来自缺页路径。
- **已完成部分**：`Device::ioctl` 改返回 syscall 侧 `crate::error::Error`，`n_tty` 的 `tcgetattr`/`tcsetattr` 不再把 uptr 错误折叠成 `EINVAL`；U 态探针两条 `EFAULT` 断言通过。
- **剩余**：`request → 参数类型` 的登记表；`framebuffer` 的裸指针。

### DF-09 uaccess 走 bounce buffer：双拷贝 + 256 KiB 上限

- **证据**：`vfs/uptr.rs` `MAX_XFER = 256 * 1024`、`MAX_PATH = 4096`；`copy_from_user`/`copy_to_user` 全部经缓冲。
- **影响**：大块 `read`/`write` 多一次内存带宽；超过 256 KiB 退化成多次 syscall（合法但低效）。内核线程路径保留零拷贝。
- **为什么接受**：临时映射用户页要在每次 `read` 改内核页表，早退路径容易漏 unmap。
- **判据**：一条 1 MiB `read` 的拷贝次数从 2 降到 1（需附录 A 的 Phase 4）。

### DF-10 `mmap` 只支持匿名映射

- **证据**：`sys_mmap` 拒绝 `MAP_SHARED`；无文件映射、`msync`、`mlock`；`librs/include/sys/mman.h` 因此只声明两个函数。
- **影响**：动态加载器、共享内存 IPC、`dlopen` 类场景不可用。
- **判据**：`mmap(MAP_PRIVATE, fd, off)` 能映射文件且写入不落盘；`msync` 生效。
- **关系**：DF-21 的前置。

### DF-17 POSIX 用例仍未整体搬进 U 态

- **证据**：`librs/tests/posix` 的用例仍由内核线程在 M 态执行；U 态覆盖目前只有 `apps/user/posix_u/posix_u.c` 的 32 条 syscall 层断言。
- **影响**：**测试与声称的能力不在同一层**。`uaccess`、`EFAULT`、特权级三条最关键的语义只被探针覆盖，C 用例本体仍验证不到；DF-02/DF-09 的修复也依赖 U 态用例。
- **判据**：`issue8_signal.c`、`issue8_fdops.c` 以 U 态进程运行；非法指针返回 `EFAULT` 且日志来自缺页路径。
- **已完成**：第一阶段（U 态进程 + 非法指针/信号/pipe/select/dup2/mmap/ioctl 共 21 条断言）；第二阶段（U 态建线程：`create_thread` U 态分支、线程退出桩、共享地址空间与 fd 表、坏参数 `EFAULT`/`EINVAL`，共 12 条断言）。`run_posix_cases` 76 passed / 0 failed，`POSIX-U-DONE` 出现。
- **剩余阻塞**：librs 的 `global_allocator` 与 `_malloc_r` 直接调 `blueos::allocator`（内核分配器），U 态不可用；`pthread` 需要 TCB/TLS（新线程 `tp` 由线程库负责）。故 C 用例本体仍跑在内核线程。

### DF-21 动态链接缺失（只有 PIE 自重定位）

- **证据**：U 态加载器能装载 `ET_DYN`/PIE 并应用 `R_RISCV_RELATIVE`（`user/mod.rs` 的 `image.is_pie` 分支），但显式拒绝 `PT_INTERP`（`genuine dynamically-linked images` 直接报错）；没有任何 `DT_NEEDED`/符号表解析；`librs` 的 `dlopen`/`dlsym` 是返回 `NULL` 的桩；应用只能从内嵌映像 `exec`，不能从文件系统加载 `.so`。
- **影响**：共享库、插件、`ld.so` 全部不可用。当前「动态」只到 PIE 自重定位。
- **判据**：分三级——
  1. 一条真实的 `-pie`/`-nostdlib` U 态用例跑通（证明 `ET_DYN` 路径可用）；
  2. `dlopen` 一个 `.so` 并能 `dlsym` 调用（需 DF-10 的文件 mmap）；
  3. `PT_INTERP` + 用户态 `ld.so`（独立立项）。
- **优先级**：在 DF-05 Phase 1+2 之后。

## P2 · 工程

### DF-11 包根没有 CI

- **证据**：包根无 `.github/`；子仓子树同步流水线已移除（DF-13）。`tools/ci/run_profile.py`、`check_changes.py` 有脚本无调度方。
- **影响**：**门禁再好，没人自动跑**——审计器、语言门禁、`check_all` 全部退化为本地手动执行。
- **判据**：删一条 POSIX 用例，CI 变红。

### DF-12 打包缺 `external/`，但有 204 处静态引用

- **证据**：构建文件中 `//external/vendor/...` 静态引用 204 处；无 `external/` 时 `gn gen` 直接失败。
- **影响**：**快照不可离线构建**，且无法靠「依赖声明重新生成」补回。
- **判据**：无网环境 `gn gen && ninja` 通过；或把 `external/` 纳入打包并给校验和。
- **缓解**：交付包默认不含 `external/`（约 328 MB），获取方式写在 README 的「打包范围」。补齐上游同版本 `external/` 后可离线构建。

### DF-14 审计器正则漏检 `POSIX_CASE_XFAIL`

- **证据**：`tools/posix_audit.py` 的模式 `\bPOSIX_CASE\s*\(` 不匹配 `POSIX_CASE_XFAIL(`；基线记 71，实际 72。
- **影响**：**删掉那条 xfail 不会变红**——最典型的作弊路径没被拦住。
- **判据**：正则同时匹配两个宏；基线数回到实际条数；删 xfail 时 `--check` 非零退出。

### DF-15 flaky 收敛未达「20 次全量」判据

- **证据**：① `test_multi_thread_mutex`（32 线程 × 32 核）偶发 U 态 illegal instruction；② `root.has_no_children()` 偶发失败；③ `qemu_mps2_an385` 的 `thread_metric` 同一二进制重跑失败集合会变。
- **影响**：U 态在高压下的稳定性**尚无证据**。任何「10 万次无逃逸」的结论都要先排除这三条。
- **已修复的根因（rv64 / `-smp 32`）**：`current_cpu_id()` 改读 `mhartid`（原先读 `tp`，每次上下文恢复被清零，所有核共用 0 号槽）；`PENDING_EXEC` 改每线程槽位（原先全局，跨核抢改写别人的 `mepc`）；`INST_ACCESS_FAULT` 不再自旋占核。
- **现状**：修复后 `run_shell_smoke` 连续 10 次全过；`run_posix_cases` 稳定。未做 20 次全量 `check_all`。本沙箱 3 核跑 `-smp 32` 仍偶发 `Count mismatch`/`Check Timeout`，属过订阅环境。
- **判据**：连续 20 次全量 `check_all` 无随机失败；或把三条显式标为 known-flaky 并从门禁隔离。

## P3 · 文档与度量

### DF-18 `report/posix_coverage.json` 是陈旧快照

- **证据**：时间 2026-11-02 21:46，早于 `posix_baseline.json`；前者显示 8 个 `missing`，当前代码已实现。
- **处理**：保留作演进留痕，标注「陈旧，非口径差异；读现状只看 `posix_baseline.json`」。
- **判据**：改名为 `posix_coverage.2026-11-02.json`，从根上消除误读。

### DF-19 Issue 8 required 仍有 2 项真实缺口：`sig2str` / `str2sig`

- **证据**：`issue8.summary.required_exported = 37 / 75`；剩余 38 = 28 编译器内建 + 8 newlib + **2 未实现**。
- **影响**：这 2 项不能算到工具链头上，因此**当前不能宣称 Issue 8 conformant**。
- **判据**：`sig2str`/`str2sig` 可链接，且 `sig2str` → `str2sig` 能往返同一信号。

---

# 第二部分 · 实施计划

> 顺序原则：**先把验证前提与架构边界做完，再补功能**。每一轮结束都必须 `run_posix_cases` 全绿 + 至少一次 `SHELL-SMOKE-PASS`。

## R1（当前）· DF-05 Phase 1+2：内核入口与 trap 路径切 S 态

目标：M 态薄固件 + S 态内核 + U 态应用。Phase 1 与 2 必须合并（MTIP 不可委托，清 `STIP` 只能在 SBI `set_timer` 里做）。

实施步骤（文件级）：

1. **新增 `arch/riscv/firmware.rs`（仅 `target_arch = "riscv64"`）**
   - M 态 `mtvec` 入口：按 hart 保存/恢复被中断的 S 态 GPR（静态数组按 `mhartid` 索引，SMP 安全），handler 用独立 M 态栈（`mret` 不恢复 `sp`）。
   - `mcause=9`（S 态 `ecall`）→ 把 `a0..a7` 送进现有 `sbi::firmware_entry`，结果写回 `a0/a1`，`mepc += 4`，`mret`。
   - `mcause=7`（MTIP）→ 先把 `mtimecmp` 停到 `u64::MAX`，再 `csrs mip, STIP`；否则 `mret` 立即重入死锁。
   - `mcause=3`（MSIP）→ 清本 hart `msip`，再 `csrs mip, SSIP`。
   - 其余 → 打印 `mcause/mepc/mtval` 后 panic。
   - `enter_kernel_s_mode()`：PMP（复用 `pmp::open_user_window()`）+ `mtvec` + `medeleg`（bits 0–8、12、13、15 = `0xB1FF`，**不委托 cause 9**，它是 SBI 通道）+ `mideleg = 0x222` + `mie = 0x888` + 清 `mip` 的 `0x222` + park CLINT + 设 `mepc` = S 入口、`MPP=S`、`MPIE=1`、`mret`（`sp` 由固件显式设置）。

2. **内核入口**：`arch_bootstrap!` 的 rv64 分支改为调用 `enter_kernel_s_mode`；`bootstrap_s` 做原 `bootstrap()` 减去 PMP，然后跳 `init`。rv32/aarch64 分支保持 M 态行为不变。

3. **trap 路径（rv64）**：`trap_entry` 与四个 save/restore 宏切 `sscratch/scause/stval/sepc/sret`；`Context` 字段 `mepc/mscratch/mstatus` 更名为 `sepc/sscratch/sstatus`（全仓约 22 处引用）；`enter_irq/leave_irq`、`local_irq_*` 用 `sstatus.SIE`/`sie`；`previous_privilege()` 读 `sstatus.SPP`。

4. **用户返回**：`enter_user`/`enter_user_from_frame` 改 `SPP=U` + `sret`，`sscratch` 语义与 M 态一致。

5. **SBI 客户端**：rv64 的 `sbi::call()` 发真实 `ecall`（`a7=ext`，`a0..a5=参数`，返回 `a0=error/a1=value`）；非 rv64 与单测仍直连 `firmware_entry`。

6. **板级**：`qemu_riscv64::init_vector_table()` 写 `stvec`；`set_timer` 走 `sbi::set_timer`，`send_ipi` 走 `sbi::send_ipi`，rv64 不再直接写 `mtimecmp`/`msip`。

验收：rv64 `run_posix_cases` 76/0，U 态探针与 fork/exec/pipe/termios 全过；`run_shell_smoke` 通过；rv32/aarch64 编译不回退。风险清单见附录 A.5。

## R2 · DF-17 第三阶段：C 用例搬进 U 态

1. librs 的 `global_allocator` 与 `_malloc_r` 从 `blueos::allocator` 改为 U 态 `mmap` 支撑（内核侧已有匿名 `mmap`）。
2. `pthread_create` 的启动 trampoline 在新线程内安装 TCB/TLS（`tp`），复用 `librs/src/tls.rs`。
3. 把 `issue8_signal.c`、`issue8_fdops.c` 作为 U 程序链接进映像，runner 只在该映像拉起，`COUNT: POSIX-U-DONE` 门禁。
4. 判据：两条 C 用例在 U 态通过，且 M 态旧路径删除（不再双跑）。

## R3 · 功能补齐（按依赖排序）

1. **DF-10 → DF-21**：文件 `mmap`（`MAP_PRIVATE`, fd, off）→ `dlopen/dlsym` → `PT_INTERP` + 用户态 `ld.so`（独立立项）。
2. **DF-08**：`ioctl` 的 `request → 参数类型` 登记表；`framebuffer` 指针改走 uaccess。
3. **DF-04 剩余**：`socketpair`、`epoll`、`mkfifo`；随后以 `busybox ash` 执行 `ls | grep` 作为判据。
4. **DF-19**：`sig2str`/`str2sig` 与往返用例。
5. **DF-06**：aarch64 EL0（工作量高于 rv64，排在 rv64 稳定之后）。

## R4 · 工程门禁（与功能并行）

1. **DF-14**：审计器正则同时匹配 `POSIX_CASE` 与 `POSIX_CASE_XFAIL`，基线回到实际条数。
2. **DF-11**：包根 CI 拉起 `run_profile.py` + `run_posix_cases`。
3. **DF-12**：`external/` 纳入打包并给校验和，或提供离线复现说明。
4. **DF-18**：陈旧覆盖度文件改名。
5. **DF-15**：连续 20 次全量无随机失败，或显式隔离 known-flaky。

---

# 附录 A · DF-05 实施依据

## A.1 先澄清一个前提

「M+U 没有 MMU，只能靠 PMP」是裸 M 态固件的教科书描述，与本仓库不符。代码事实：M 态直接写 `satp`、每进程切地址空间、完整 Sv39 与 COW。**隔离早就有了。** 迁移真正要解决的只有三件事：① 故障恢复（M 态最高特权无兜底）；② 内核自身虚拟化（M 态不翻译，无 KPTI/ASLR）；③ 透明 uaccess（`MPRV+SUM` 或双页表，替代 bounce buffer）。

## A.2 迁移改动面

| # | 现状 | 迁移后 |
| --- | --- | --- |
| A | trap 全在 M 态（`mret`/`mcause`/`mepc`/`mscratch`/`MPP`） | 新增 S 态向量（`stvec`/`sret`/`scause`/`sepc`/`sscratch`/`SPP`）；M 态只留 machine trap 转发 |
| B | 时钟用机器级 `mtimecmp` | 经 SBI `set_timer`，S 态收 `sip.STIP` |
| C | IPI 直接写 `msip` | 经 SBI `send_ipi`/`clear_ipi`，S 态收 `sip.SSIP` |
| D | `enter_user` 用 `MPP=U` + `mret` | 改 `SPP=U` + `sret`；`enter_irq`/`leave_irq` 改 `sstatus` |
| E | PMP 由内核在 M 态配置 | 收归固件；S 态内核不再碰 PMP |
| F | 早期启动直接 M 态跑内核 | 固件做完 PMP/栈后 `mret` 带 `MPP=S` 进内核 |
| G | `previous_privilege()` 读 `mstatus.MPP` | 改读 `sstatus.SPP` |
| H | S 态内核自映射 PTE 必须 `U=0` | `U=1` 页在 `SUM=0` 下 S 态不可访问 |

## A.3 Phase 0 实测结论（设计依据，非待办）

`tools/smode_probe/` 在 `-bios none` 下实测：能进 S 态；`ecall` 路由到 M 态 `mtvec`；`medeleg` 后 `stvec`/`sret` 可用；S 态 `satp` 生效；MTIP 不可委托、必须由 M 转 `STIP`；`mret` 前必须 park `mtimecmp`；`mret` 不恢复 `sp`。

探针暴露的三个坑：① S 态映射自身的 PTE 必须 `U=0`（否则开 `satp` 立即取指 fault，`mcause=12`）；② `satp.PPN` 在 bits 43:0、`PTE.PPN` 在 bits 53:10，差 `<<10`；③ M 态 handler 与 S 态不能共用栈，`medeleg` 只能由 M 态写。

## A.4 后续阶段

| 阶段 | 内容 | 验收 |
| --- | --- | --- |
| 1+2（R1） | 内核入口切 S 态 + trap 路径迁移 + 时钟/IPI 改经 SBI | U 态应用照常在 S 态内核上跑；多核调度与抢占无回归 |
| 3 | PMP 收归 M 态固件并收紧窗口 | U 态越权访问机器内存被拦下；与 DF-07 同批 |
| 4（可选） | 内核虚拟化（高半区、KPTI）+ 透明 uaccess | 1 MiB `read` 拷贝次数 2 → 1（DF-09） |
| 5 | aarch64 对称分层 + 全回归 | 需先补 EL0（DF-06），再补常驻 EL2 固件 |

## A.5 风险

1. **全平台回归**：rv64c/e/f/g、aarch64 的 `check_all` 与 `run_posix_cases` 不得回退；用 DF-15 的已知 flake 区分「真回归」与「负载偶发」。
2. **时序/竞态**：`mtimecmp → SBI set_timer` 的 deadline 传递、`msip → SBI send_ipi` 的 SMP 竞态。
3. **上下文切换语义**：`mscratch`/`sscratch` 在嵌套 trap 与切换时的角色对齐，避免「内核栈被当作用户栈」。
4. **编译目标 spec**：异常向量段 `.trap.handler` 要对应 `stvec`，链接脚本随之调整。
5. **验证环境**：内核二进制改动需在容器内构建 + QEMU 验证；宿主机只能验证纯文本/Python 产物。

## A.6 整体结项

- [ ] M 态固件可独立复位/重启 S 态内核（故障恢复达成）。
- [ ] 三层运行，U 态进程间隔离与 U→机器内存隔离由 PMP 保证。
- [ ] rv64 与 aarch64 全部 `check_all`、`run_posix_cases` 绿，信号与 POSIX 用例无回归。
- [ ] （可选 Phase 4）内核虚拟化 + 透明 uaccess 落地，uaccess 路径仍对 U 态指针安全。
