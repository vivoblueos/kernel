# Buddy 单元测试实现计划

## 1. 目标

建立一套分层的 buddy 测试，同时满足：

- buddy 算法测试使用独立局部实例，用例之间没有状态共享，可并行执行。
- 覆盖初始化、分裂、合并、对齐分配、耗尽恢复、边界与错误输入。
- wrapper 测试覆盖 PFN/物理地址转换和真实 backing memory 读写。
- 仅少量内核集成测试使用全局 `BUDDY_ALLOC`，不把所有 buddy 算法测试串行化。
- 测试失败时能区分是算法、kernel wrapper、地址映射，还是 `KernelAllocator` 路由问题。

## 2. 非目标

- 不通过单元测试验证非法 `unsafe` 调用，例如 double free、使用错误 order 释放、释放其他 allocator 的 frame。这些已属于 API safety contract，而当前测试使用 panic-abort，也不适合使用 `catch_unwind` 验证。
- 不在每个 buddy 单元测试中耗尽全局物理内存。
- 不为了测试暴露 `PageDescriptor` 内部结构；优先通过可观测行为验证算法。

## 3. 当前状态与约束

1. `allocator/src/buddy.rs` 中的 raw buddy 测试位于整块注释内，当前实际不会编译或执行。
2. `allocator_crate` 是 `kernel_unittest` 的依赖 crate；`cfg(test)` 不会从顶层 kernel crate 传递给依赖。因此，仅取消 raw buddy 测试的注释，不能让它们进入现有 `kernel_unittest` 镜像。
3. 内核单元测试使用 `blueos_test_macro::test`，并且测试线程栈较小；metadata 和 backing memory 不能作为大数组放在栈上。
4. `BuddyAllocator::init` 初始化了自引用的 intrusive list sentinel，allocator 初始化后必须保持稳定地址。测试 fixture 中的 allocator 必须在 `Box`/`Pin` 中定位后再调用 `init`。
5. `Box` 和 `alloc::alloc::alloc` 使用内核全局 allocator。局部 fixture 的内部状态是隔离的，但 fixture 建立和销毁仍会短暂访问全局 buddy。

## 4. 测试分层

### 4.1 Raw buddy 算法测试

位置：`kernel/src/allocator/buddy/tests.rs`。

测试直接使用 `allocator_crate::buddy::BuddyAllocator` 的公开 API。每个用例创建自己的 `RawBuddyFixture`，拥有：

- 定位后的 `BuddyAllocator`。
- 根据 `BuddyAllocator::metadata_layout(total_pages)` 动态分配的 metadata buffer。
- metadata 的 `Layout`，供 `Drop` 时使用原始 layout 释放。
- 初始化时使用的 manageable PFN range。

`RawBuddyFixture` 提供统一的不变量检查：

```text
total_pages == free_pages + used_pages + reserved_pages
reserved_pages == total_pages - manageable_range.len()
已分配区间两两不重叠
已分配区间全部位于 manageable range
```

这一层不需要真实页数据，因为 raw buddy 的契约只是管理 PFN 和 metadata。

### 4.2 Kernel wrapper 与 backing memory 测试

位置：`kernel/src/allocator/buddy/tests.rs`。

创建 `BuddyTestArena`，使用一段按页对齐、连续且由 fixture 独占的真实内存：

```text
arena virtual/physical base
│
├─ metadata pages（reserved）
│
└─ manageable data pages
```

实现要点：

1. arena 总大小取 2 的幂，使用 `Layout(size, PAGE_SIZE)` 从全局 allocator 一次性保留连续内存。
2. metadata 放在 arena 前部，`manageable_start_pfn` 按 metadata 占用页数向上取整，避免 metadata 与可分配数据页重叠。
3. 使用 `kernel_virt_to_phys(arena_base)` 作为 `BuddyHeap::init_for_test` 的 `phys_base`。
4. 通过 `alloc_pages_phys_addr` 取得物理地址，再使用 `kernel_phys_to_virt` 转回可读写指针。
5. fixture 销毁顺序必须是：先停止使用局部 heap，再释放 arena。如果字段自动 drop 顺序不够直观，使用显式 `Drop`/`ManuallyDrop` 表达所有权关系。
6. arena 不放在测试线程栈上。数据读写 fixture 使用小规模 arena，默认 16 或 32 页，避免并行测试时消耗大量全局内存。

### 4.3 全局 allocator 集成测试

位置：`kernel/src/allocator/mod.rs` 现有测试模块。

只保留少量必须经过全局 `BUDDY_ALLOC` 和 `KernelAllocator` 的测试：

- 大对齐或大于 buddy threshold 的 allocation 能获得页对齐内存。
- 分配的内存可读写，并能读回写入的 pattern。
- 两个同时存活的 allocation 不重叠，向其中一个写入不会改变另一个。
- realloc 跨越 buddy threshold 时保留原有内容。
- realloc 失败时原 allocation 仍然有效。

集成测试优先使用“返回值和自己持有的 allocation”作断言，不依赖全局瞬时 `used_pages` 精确值。这类所有权局部的断言本身可以与其他内存使用者并行。

## 5. 全局状态门禁

仅当集成测试必须检查以下全局不变量时，才使用测试专用独占门禁：

- 某次操作前后 `used_pages` 的精确差值。
- 全局空闲页耗尽。
- 要求整个多步骤序列期间全局 buddy 无其他变化。

不复用 `origin/main` 中“先读 owner，然后获取 allocator lock”的 check-then-act 实现。如果确实需要门禁，按以下协议实现：

1. 普通 buddy 操作进入时注册 active reader，在持有 reader guard 期间完成整个内部 allocator 操作。
2. 注册 reader 后再次检查 exclusive owner；若 owner 已改变，撤销 reader 并重试，关闭 check-then-act 窗口。
3. 独占方先发布 owner，再等待 active reader 归零，之后才返回 exclusive guard。
4. owner 线程允许重入，以便测试中的 `Vec`/`Box` 等间接分配不会自锁。
5. owner 标识不得与“无 owner”的零值冲突；若 thread id 可能为零，存储时要进行非零编码。
6. 所有 guard 使用 RAII 释放，不让 assertion failure 遗留 owner 或 active reader。

门禁仅在 `cfg(test)` 下存在。若删除精确全局计数断言后已无用例需要它，则不实现门禁，避免增加不必要的测试专用同步逻辑。

## 6. 测试用例矩阵

### 6.1 Raw buddy 必需用例

- [x] 未初始化 allocator 的 `memory_info` 全为零。
- [x] `metadata_layout` 拒绝零页和溢出页数。
- [x] `init` 拒绝 metadata 太小、未对齐、非法 manageable range 和重复初始化。
- [x] 非 2 的幂页数、非对齐 manageable start/end 的初始统计正确。
- [x] 每个受支持 order 的分配地址对齐，分配/释放前后页数守恒。
- [x] `order > MAX_ORDER` 和 `align_order > MAX_ORDER` 返回 `None`。
- [x] aligned allocation 同时满足 block size 和请求对齐。
- [x] 按 order 0 耗尽局部 allocator，再全部释放，空闲页完整恢复。
- [x] 释放相邻 buddy 后可成功分配更大 order，从可观测行为证明 coalesce。
- [x] 不同释放顺序（正序、逆序、交错）都不泄漏页。
- [x] manageable range 边缘的 buddy 不会跨越 reserved 区域合并。
- [x] 重复混合 order 分配/释放序列后恢复初始状态。
- [x] 使用固定种子的轻量级 deterministic stress：维护一个简单 bitmap/reference model，每次操作后检查无重叠与页数守恒。

### 6.2 Wrapper/backing memory 必需用例

- [x] `phys_to_pfn`/`pfn_to_phys` 在 base、最后一页、未对齐地址、范围外地址的结果正确。
- [x] `phys_base + (pfn << PAGE_SHIFT)` 溢出时 `pfn_to_phys` 返回 `None`。
- [x] 分配 order 0 和多页 block，对首字节、页边界、最后字节写入并读回 pattern。
- [x] 同时分配两个 block，写入不同 pattern，验证互不污染。
- [x] 释放其中一个 block 后，另一个存活 block 的内容不变。
- [x] 所有返回地址都位于 arena manageable data 区，不覆盖 metadata pages。
- [x] 两个独立 fixture 在两个测试线程中同时分配/写入/释放，各自统计回到初始值。
- [x] 多线程共享同一个局部 `BuddyHeap` 进行分配/释放，验证 wrapper 的 `SpinLock` 同步和最终页数守恒。

### 6.3 全局集成必需用例

- [x] `KernelAllocator` 的大小和对齐路由边界正确。
- [x] buddy 路由返回的真实内存可读写且满足对齐。
- [x] heap → buddy、buddy → heap 的 realloc 保留 `min(old_size, new_size)` 内容。
- [x] buddy order 变化的 realloc 保留内容。
- [x] realloc 失败不释放或修改原 block。

## 7. 预计文件变更

### `allocator/src/buddy.rs`

- 删除当前整块注释的测试代码，避免它与实际可执行测试分叉。
- 除非某个关键不变量无法通过公开行为验证，否则不增加测试专用的 metadata 窥探 API。

### `kernel/src/allocator/buddy/mod.rs`

- 保留全局 `BUDDY_ALLOC` 声明。
- 把内联的单个测试替换为 `#[cfg(test)] mod tests;`，减少模块本体噪音。

### `kernel/src/allocator/buddy/tests.rs`

- 新增 `RawBuddyFixture`、`BuddyTestArena` 和通用断言辅助函数。
- 实现 raw buddy 与 wrapper/backing memory 测试矩阵。
- 所有测试使用 `blueos_test_macro::test`，确保被收集到当前 kernel test harness。

### `kernel/src/allocator/buddy/heap.rs`

- 保留 `init_for_test`，补充 safety 文档：metadata/backing 所有权、heap 稳定地址、初始化后 translation 不再变更。
- 如果测试需要非“保留前缀”的 manageable range，再将 `manageable_start_pfn` 扩展为 `Range<usize>`；不为预留需求提前扩展 API。
- 只在存在全局状态断言时增加 `cfg(test)` 门禁。

### `kernel/src/allocator/mod.rs`

- 保留与整理真实内存及 realloc 集成测试。
- 将 `buddy_routing_uses_both_size_and_alignment` 的精确全局 `used_pages` 断言改成所有权局部的验证；如无法保持同等覆盖，才让该用例获取独占门禁。

## 8. 实施顺序

### 阶段 A：建立可执行的 raw buddy 测试

- [x] 新建 `kernel/src/allocator/buddy/tests.rs`。
- [x] 实现稳定地址、对齐正确、RAII 释放的 `RawBuddyFixture`。
- [x] 迁移并改写已注释的 raw buddy 用例。
- [x] 补齐 manageable range 边界、aligned allocation 与 deterministic stress。
- [x] 删除 `allocator/src/buddy.rs` 中不可执行的注释测试块。

验收：所有 raw buddy 用例都在 kernel unittest 输出中可见，且每个用例只依赖自己的 buddy 状态。

### 阶段 B：加入真实 backing memory

- [x] 实现 `BuddyTestArena`。
- [x] 校验 metadata pages 与 manageable data pages 不重叠。
- [x] 实现真实页内容读写、块不重叠和存活 allocation 不受其他 free 影响的测试。
- [x] 实现独立 fixture 并行测试和共享局部 heap 并发测试。

验收：局部 buddy 测试可以读写真实内存，同时不依赖全局 buddy 的瞬时统计或内部状态。

### 阶段 C：整理全局集成测试

- [x] 复查 `kernel/src/allocator/mod.rs` 中所有依赖全局 buddy 的断言。
- [x] 将能改为所有权局部断言的用例改写为无锁并行安全形式。
- [x] 复查后已消除精确全局计数断言，不再存在必须独占的多步骤全局不变量，因此未增加测试门禁。
- [x] 删除重复于 raw buddy 层的全局 split/coalesce/exhaustion 测试。

验收：全局集成测试数量少、职责明确，不会为算法测试引入大范围串行化。

### 阶段 D：多配置验证

- [x] 运行 rustfmt 并检查 `git diff --check`。
- [x] 在已配置的 AArch64 QEMU 目录运行 `ninja -C out/qemu_virt64_aarch64.release.swi run_unittest`。
- [x] 至少再选择一个 32 位目标编译和运行 unittest，覆盖 `usize`、地址溢出与小内存配置。
- [x] 运行 `kernel_unittest_clippy` 或对应 `check_kernel_by_clippy` 目标。
- [x] 对并发用例进行多次 repeat/stress 运行，确认无偶发统计差异、死锁或内存耗尽。

## 9. 完成标准

- raw buddy 的正常路径、边界、错误初始化、split/coalesce、alignment 和 exhaustion 都有可执行测试。
- 局部 wrapper 测试对 buddy 管理的真实 backing memory 进行了页边界读写。
- 所有算法测试不读写全局 buddy 的 metadata，用例之间无共享算法状态。
- 全局集成测试不依赖可被其他测试改变的瞬时计数，或者在必要时使用无竞态的独占门禁。
- fixture 对 metadata/backing memory 的对齐、稳定地址、生命周期和释放 layout 有明确的 safety 注释。
- AArch64 和至少一个 32 位目标通过编译与 unittest，并通过格式和 clippy 检查。
