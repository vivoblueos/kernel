// Copyright (c) 2026 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//       http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

mod config;
use crate::arch::riscv::{local_irq_enabled, trap_entry, Context};
use blueos_driver::uart::esp32_usb_serial::Esp32UsbSerialIsr;
use blueos_hal::{isr::IsrDesc, Has8bitDataReg};

// 调度时钟源:systimer(同 C3,driver 见 blueos_driver::systimer::esp32_sys_timer)。
// C6 systimer base = 0x6000_A000(TRM 第 11 章 System Timer,C3 是 0x6002_3000),
// 计数频率 = 16 MHz(systimer 固定 16MHz 计数,UNI_EN 使能后计数器自增)。
// 16_000_000 % TICKS_PER_SECOND(100) = 0,满足 time.rs 的整除断言。
// target0 比较 match 后置 INT_RAW.bit0 → 经 INTMTX 路由到 CPU 线 16 →
// PLIC_MX 使能/优先级仲裁 → mip.MEIP → trap 兜底分支 → handle_intc_irq。
// driver impl Clock trait 的 4 方法(hz/estimate_current_cycles/interrupt_at/stop),
// 另有 inherent 方法 clear_interrupt() 供 handle_intc_irq 清 INT_RAW.bit0。
pub type ClockImpl =
    blueos_driver::systimer::esp32_sys_timer::Esp32SysTimer<0x6000_A000, 16_000_000>;

core::arch::global_asm!(
    "
.section .trap
.type _vector_table, @function

.option push
.balign 0x4
.option norelax
.option norvc

_vector_table:
    j {trap_entry}          // 0: Exception
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    j {trap_entry}
    ",
    trap_entry = sym trap_entry,
);

#[inline]
fn init_vector_table() {
    unsafe extern "C" {
        static _vector_table: u32;
    }
    let mut v = core::ptr::addr_of!(_vector_table) as usize;
    v |= 1; // set the least significant bit to enable vectored mode
    unsafe {
        core::arch::asm!(
            "csrw mtvec, {0}",
            in(reg) v,
            options(nostack, preserves_flags),
        );
    }
}

/// PLIC_MX:C6 真正的 M 模式中断控制器(base 0x2000_1000,esp-idf DR_REG_PLIC_MX_BASE)。
/// 外部中断(USB/systimer)经此递交到 CPU:外设源 → INTMTX MAP 路由 →
/// PLIC_MX 使能/优先级/阈值仲裁 → mip.MEIP → trap(mcause 低字节=CPU 线号)。
///
/// **C6 真正的 M 模式中断仲裁器是 PLIC_MX @ 0x2000_1000**(esp-idf
/// DR_REG_PLIC_MX_BASE,esp-idf interrupt.c 实际配的就是它)。
/// 注意:esp-idf 还有个 `DR_REG_INTPRI_BASE=0x600C_5000`——实测那块地址接受
/// 写入/能读回(所以早期 dump 里 ENABLE/THRESH/PRI "看起来全对"),但它**不
/// 控制 mip.MEIP**,是个影子寄存器块。早期板级误用 0x600C_5000,导致 INT_ST=1
/// 却 EIP=0、meip=0、中断永不进 trap。实测坐实后改回 PLIC_MX。
///
/// 寄存器布局(esp-idf plic_reg.h 核实):
///   ENABLE      @ +0x0        (PLIC_MXINT_ENABLE_REG, bit[n]=line n 使能)
///   TYPE        @ +0x4        (PLIC_MXINT_TYPE_REG, bit[n]=0 level/1 edge)
///   CLEAR       @ +0x8        (PLIC_MXINT_CLEAR_REG, write-1-to-clear per line)
///   EIP_STATUS  @ +0xC        (PLIC_EMIP_STATUS_REG, RO, bit[n]=line n pending)
///   PRI[n]      @ +0x10 + n*4 (PLIC_MXINTn_PRI_REG, 4-bit 优先级字段 [3:0])
///   THRESH      @ +0x90       (PLIC_MXINT_THRESH_REG, [7:0] 阈值,优先级>阈值才递交)
///   CLAIM       @ +0x94       (PLIC_MXINT_CLAIM_REG, esp-idf 运行时不读,硬件自动清 pending)
const PLIC_MX_BASE: usize = 0x2000_1000;
const PLIC_MX_ENABLE: usize = PLIC_MX_BASE + 0x0;
const PLIC_MX_TYPE: usize = PLIC_MX_BASE + 0x4;
const PLIC_MX_CLEAR: usize = PLIC_MX_BASE + 0x8;
const PLIC_MX_EIP_STATUS: usize = PLIC_MX_BASE + 0xC;
const PLIC_MX_PRI: usize = PLIC_MX_BASE + 0x10; // PRI[line] @ PLIC_MX_PRI + line*4
const PLIC_MX_THRESH: usize = PLIC_MX_BASE + 0x90;

/// mideleg CSR(0x303)的外部中断委托位——C6 中断不进 trap 的真根因之一。
/// TRM PDF p42 Register 1.7:mideleg 复位 0x00000111 = bit0(U software)
/// |bit4(U timer)|bit8(U external)。TRM 1.6.2 属性:mideleg bit **置位→委托
/// U 模式**(pending 走 uip);**清零→M 模式捕获**(pending 走 mip)。BlueOS 是
/// M 模式单体内核([arch/riscv/mod.rs:41]),只开 mie 从不开 uie,委托位=1 时
/// pending 卡在 uip 既不被 M 也不被 U 服务,M 模式 trap 永不触发。
///
/// **bit8(外部委托)是关键**:systimer timer 和 USB RX 都走外部中断,bit8=1 时
/// 外部中断 pending 走 uip.UXIP 不进 mip.MEIP(bit11)——必须清零归 M 模式,
/// bootstrap 开的 mie.MEIE(bit11)才对 M 模式 pending 有效。bit4(timer 委托)、
/// bit0(software 委托)无副作用,一并清零。mideleg 是 R/W,csrc 合法。
/// 一次性 csrc 0x111 清三委托位,所有中断统一归 M 模式。
const MIDELEG_UEXT_BIT: usize = 1 << 8;
const MIDELEG_UTIMER_BIT: usize = 1 << 4;
const MIDELEG_USOFT_BIT: usize = 1 << 0;
/// 一次性清零 mideleg 复位值 0x111 的三个委托位(bit0|bit4|bit8)。
const MIDELEG_DELEG_MASK: usize = MIDELEG_USOFT_BIT | MIDELEG_UTIMER_BIT | MIDELEG_UEXT_BIT;

/// INTERRUPT_MATRIX(INTMTX,TRM 1.6,base 0x6001_0000):源→CPU 线路由器。
/// 每个外设源有一个专用 MAP 寄存器,5-bit 字段 [4:0] 选目标 CPU 线(0..31)。
/// MAP 偏移不连续(有空洞),故按绝对偏移编程。C3 把路由做在 Esp32Intc 里
/// (走 C3 的 INTPRI 布局),C6 的 PLIC_MX 布局不同不能复用,故这里用裸写。
const INTMTX_BASE: usize = 0x6001_0000;
/// USB_SERIAL_JTAG 源 → CPU 线(MAP 寄存器 @ INTMTX_BASE + 0xC0)。
const INTMTX_USB_SERIAL_JTAG_MAP: usize = INTMTX_BASE + 0xC0;
/// SYSTIMER_TARGET0 源(源号 57)→ CPU 线 16(MAP 寄存器 @ INTMTX_BASE + 0xE4)。
const INTMTX_SYSTIMER_TARGET0_MAP: usize = INTMTX_BASE + 0xE4;

/// systimer target0 路由到的 CPU 线号(同 C3 约定)。
/// handle_intc_irq 用 `mcause & 0xff` 匹配此线号,调 ClockImpl::clear_interrupt +
/// handle_clock_interrupt。systimer target0 中断走外部中断路径,不占 mcause=7。
const TARGET0_INT_NUM: usize = 16;

/* Watchdog timers enabled by the bootloader in flash-boot mode. Unlike C3
   (whose RTC WDT lives in RTC_CNTL at 0x6000_8000), C6 splits its watchdogs:
   the RTC/low-power watchdog moved to the LP_WDT block at 0x600B_1C00, while
   0x6000_8000 is now Timer Group 0 (TIMG0), whose MWDT is *also* kept running
   by the bootloader. If neither is disabled, the flash-boot watchdog fires a
   few hundred ms after the app starts — the chip resets, the USB-Serial-JTAG
   CDC port re-enumerates, and the host monitor (espflash) dies with a
   `Broken pipe` read error. This is the C6 analogue of C3's RTC WDT-disable
   block (see seeed_xiao_esp32c3/mod.rs). Addresses from esp-idf
   soc/esp32c6/register/soc/reg_base.h + lp_wdt_reg.h.

   LP_WDT layout: wdtconfig0 @ +0x00, wdtwprotect @ +0x18. wdt_en is bit 31,
   wdt_flashboot_mod_en is bit 12. Both WDTs share the write-protect unlock
   key 0x50D8_3AA1 (same as C3, confirmed in esp-hal rtc_cntl/timg drivers).

   TIMG0 MWDT layout (standard across ESP32 chips, used by esp-hal timg.rs):
   wdtconfig0 @ +0x48, wdtwprotect @ +0x64, wdt_en bit 31. */
const LP_WDT_BASE: usize = 0x600B_1C00;
const LP_WDT_CONFIG0: usize = LP_WDT_BASE + 0x00;
const LP_WDT_WPROTECT: usize = LP_WDT_BASE + 0x18;
const TIMG0_BASE: usize = 0x6000_8000;
const TIMG0_WDT_CONFIG0: usize = TIMG0_BASE + 0x48;
const TIMG0_WDT_WPROTECT: usize = TIMG0_BASE + 0x64;
const WDT_WKEY: u32 = 0x50D8_3AA1;
const WDT_EN_BIT: u32 = 1 << 31; // bit 31 in both WDTCONFIG0 registers
// flash-boot 模式位(PDF 13.2.2.4):flash boot 后 MWDT0/RWDT 自动使能,
// 必须清这两个位才能停 flash-boot 保护流程。MWDT0 在 TIMG_WDTCONFIG0、
// RWDT 在 LP_WDT_RWDT_CONFIG0。位号经 PDF Register 12.10/13.1 bitfield 核实。
const WDT_FLASHBOOT_MOD_EN_BIT: u32 = 1 << 12; // bit 12

/// CPU 中断线号。C6 把 CPU 线号(不是 RISC-V cause 11)塞进外部中断的 mcause,
/// 故 trap.rs 的 `#[cfg(not(has_plic))]` 分支把 mcause 交给 handle_intc_irq,
/// 这里用 `mcause & 0xff` 匹配。沿用 C3 的线号约定(USB→15、systimer→16)方便对照。
/// 时钟中断走 systimer target0(线 16),也占外部线——与 C3 同构。
const USB_SERIAL_JTAG_INT_NUM: usize = 15;

#[inline]
unsafe fn write32(addr: usize, val: u32) {
    unsafe { core::ptr::write_volatile(addr as *mut u32, val) };
}

#[inline]
unsafe fn read32(addr: usize) -> u32 {
    unsafe { core::ptr::read_volatile(addr as *const u32) }
}

/// 按 TRM 1.6.3.2 "配置一个外部中断"步骤,把外设源路由到 CPU 线并配置 PLIC_MX:
///   1.save MIE / clear MIE      ——避免配置中途触发中断
///   2.TYPE bit n                ——0=level(USB RX 是 level 型)/1=edge
///   3.PRI_n = 1~15              ——4 位优先级字段
///   4.ENABLE bit n              ——使能该线(PLIC_MX 内部使能)
///   4.5.mie bit n               ——per-line mie 使能(C6 PLIC 变体特有,见下方)
///   5.FENCE                     ——确保写序对中断控制器可见
///   6.restore MIE
/// `map_reg` 是源的 INTMTX MAP 寄存器地址(不是 source_id*4)。
///
/// step 4.5 是 C6 PLIC 变体与标准 RISC-V PLIC 的关键差异:标准 PLIC 所有外部中断
/// 共享一个 mie.MEIE(bit11)总开关;而 Espressif C6 每条外部中断线在 mie CSR 里有
/// 独立的 per-line 使能位(位号 = 线号,如 USB 线15 → mie.bit15)。
/// 只开 PLIC_MX 内部 ENABLE 而不置 mie 对应位,则 PLIC EIP 升起却传不到 mip.MEIP,
/// CPU 永不进 trap(实测 mie=0x888,bit15/16=0,USB/systimer 全哑)。
/// 依据:ROM esprv_intc_int_enable @0x4002914c 反汇编——末尾 `csrrs mie,a0` 即此操作。
unsafe fn route_source(map_reg: usize, line: usize, prio: u32) {
    unsafe {
        // (1) save/clear MIE——TRM 1.6.3.2 step1。init 起始已断言 mie=0,
        //     save/clear 是保留 TRM 流程语义的安全冗余。
        // mie 标 mut:step 4.5 要把 per-line 位或进此变量,再由 step 6 restore 写回 CSR。
        let mut mie: usize;
        core::arch::asm!(
            "csrr {mie}, mie",
            "csrw mie, zero",
            mie = out(reg) mie,
            options(nostack, preserves_flags),
        );
        // INTMTX MAP:[4:0]=目标 CPU 线。
        write32(map_reg, line as u32);
        // (2) TYPE bit n:显式写 0=level(USB_SERIAL_JTAG RX 是 level 型中断)。
        let t = read32(PLIC_MX_TYPE);
        write32(PLIC_MX_TYPE, t & !(1u32 << line));
        // (3) PRI_n:4 位优先级字段 [3:0],取值 1~15。
        write32(PLIC_MX_PRI + line * 4, prio & 0xF);
        // (4) ENABLE bit n:在 32 线使能位图里置该线位。
        let en = read32(PLIC_MX_ENABLE);
        write32(PLIC_MX_ENABLE, en | (1u32 << line));
        // (4.5) per-line mie 使能——Espressif C6 PLIC 变体特有(见函数头注释):
        //   置 mie.bit_n(n=line),否则 PLIC EIP 传不到 mip.MEIP、CPU 不进 trap。
        //   注意:此处只改保存的 `mie` 变量、不碰 mie CSR。因为 route_source 采用
        //   save/clear/restore 模型:step 1 清零 CSR、step 6 用保存值覆盖回 CSR——
        //   若在此刻直接 csrrs 写 CSR,step 6 会把新位覆盖丢失(实测 mie 仍=0x888)。
        //   改变量后,step 6 把"含新位的旧值"写回,时机也正确(route_source 在 init
        //   阶段调用,全局 mstatus.MIE=0,真正使能是 init 末尾开 mstatus.MIE 时)。
        //   多次调用(USB 线15、systimer 线16)能累积:下次 save 读到本次写回的值。
        mie |= 1usize << line;
        // (5) FENCE——TRM 1.6.3.2 step5,确保上述写序对中断控制器可见。
        core::arch::asm!("fence io, io", options(nostack, preserves_flags));
        // (6) restore MIE。
        core::arch::asm!(
            "csrw mie, {mie}",
            mie = in(reg) mie,
            options(nostack, preserves_flags),
        );
    }
}

/// Disable one watchdog: unlock writes, clear the enable bit (and the
/// flash-boot-mode bit on LP_WDT), then re-lock. `flashboot_mask` is ORed in
/// so LP_WDT also clears `wdt_flashboot_mod_en` (bit 12); pass 0 for TIMG0.
#[inline]
unsafe fn disable_wdt(wprotect: usize, config0: usize, flashboot_mask: u32) {
    unsafe {
        write32(wprotect, WDT_WKEY); // unlock
        let cfg = read32(config0);
        write32(config0, cfg & !(WDT_EN_BIT | flashboot_mask));
        write32(wprotect, 0); // re-lock
    }
}

/// 外部中断处理——trap.rs `#[cfg(not(has_plic))]` 分派到此。
/// 按 mcause 低字节(CPU 线号)分派(同 C3 模型)。systimer target0(线 16)和
/// USB_SERIAL_JTAG(线 15)都走外部中断,在此统一分派。
pub(crate) fn handle_intc_irq(ctx: &Context, mcause: usize, mtval: usize) {
    let _ = (ctx, mtval);
    match mcause & 0xff {
        // systimer target0:先清 INT_RAW.bit0(driver 内部写 INT_CLR),再走统一时钟中断入口。
        TARGET0_INT_NUM => {
            ClockImpl::clear_interrupt();
            crate::time::handle_clock_interrupt();
        }
        USB_SERIAL_JTAG_INT_NUM => {
            ESP32_USB_SERIAL_ISR.service_isr();
        }
        _ => {}
    }
}

pub(crate) fn init() {
    assert!(!local_irq_enabled());

    crate::boot::init_runtime();
    crate::boot::init_heap();
    init_vector_table();

    // systimer 起振(同 C3):driver 内部使能 UNI_EN 让计数器自增、配 target0 比较。
    // 调度时钟中断路径:systimer target0 match → INT_RAW.bit0 → INTMTX 路由(下方)
    // → PLIC_MX 仲裁 → mip.MEIP(bit11)→ trap 兜底分支 → handle_intc_irq(线16)。
    blueos_driver::systimer::esp32_sys_timer::Esp32SysTimer::<0x6000_A000, 16_000_000>::init();

    // 外部中断路由 + PLIC_MX 六步配置(TRM 1.6.3.2)。阈值=1、优先级=15(照搬 C3):
    //   USB_SERIAL_JTAG(线15) —— host 输入经此进 handle_intc_irq
    //   SYSTIMER_TARGET0(线16) —— 调度时钟经此进 handle_intc_irq
    // 两者都走外部中断(mcause 高位=1),trap.rs `#[cfg(not(has_plic))]` 兜底分派。
    unsafe {
        write32(PLIC_MX_THRESH, 1);
        route_source(INTMTX_USB_SERIAL_JTAG_MAP, USB_SERIAL_JTAG_INT_NUM, 15);
        route_source(INTMTX_SYSTIMER_TARGET0_MAP, TARGET0_INT_NUM, 15);
    }

    // mideleg 归 M 模式——外部中断进 trap 的前提。mideleg 复位 0x111 = bit0|bit4|bit8:
    //   bit8 = U external  → 置位时外部中断 pending 走 uip.UXIP,不进 mip.MEIP(bit11)
    //   bit4 = U timer     → 置位时 timer pending 走 uip.UTIP
    //   bit0 = U software  → 置位时软件中断 pending 走 uip.USIP
    // systimer timer 和 USB RX 都走外部中断,bit8 若不清,pending 卡在 uip 既不被 M
    // 也不被 U 服务(BlueOS 是 M 模式单体内核、只开 mie 从不开 uie),trap 永不触发。
    // bit4/bit0 一并清零无害。一次性 csrc 0x111 三委托位全归 M 模式,mie 才能解屏蔽。
    // 时序安全:mstatus.MIE 此刻仍为 0(上方断言),改委托位不触发中断。
    unsafe {
        core::arch::asm!(
            "csrc mideleg, {mask}",
            mask = in(reg) MIDELEG_DELEG_MASK,
            options(nostack, preserves_flags),
        );
    }

    // mie 放行外部中断:bootstrap 的 #[cfg(has_mie)] 已 `csrs mie, MTIE|MSIE|MEIE`
    // ([arch/riscv/mod.rs:480]),其中 MEIE=bit11 即机器外部中断聚合使能——systimer
    // timer 和 USB RX 都经 mip.MEIP(bit11)递交,必须 mie.MEIE 放行。bootstrap 已开对,
    // 板级无需再补。前置条件:mideleg bit8 已上方清零,外部中断归 M 模式后 mie.MEIE
    // 才对 M 模式 pending 有效。

    // 设第一个 systimer target0 deadline——打破首次 trap 死锁。
    // driver 起振后计数器自增,但首个比较 deadline 仍需有人设:否则 target0 永不 match,
    // INT_RAW.bit0 不置位,首个时钟 trap 不进,handle_clock_interrupt 不被调,后续
    // deadline 也永无人设——死锁。init 主动设第一个近期 deadline(now+1 tick=10ms),
    // 首个 trap 触发后由 handle_clock_interrupt([time.rs:99])接管设后续。
    // 时序安全:mstatus.MIE 此刻仍为 0(上方断言),设 deadline 不会立即触发中断,
    // 待 schedule() 开 mstatus.MIE 后 10ms 内首个 trap 触发。
    crate::time::Tick::interrupt_after(crate::time::Tick(1));

    // 禁用 bootloader 留下的两个看门狗(LP_WDT + TIMG0),否则启动后几百 ms 复位,
    // 把主机串口监视器杀成 `Broken pipe`。NOTE: 本板 CONFIG_ENABLE_NET=n,
    // 没有 radio 要拉起,故省略 WiFi/电源域初始化。
    unsafe {
        // LP_WDT:同时清 wdt_flashboot_mod_en(bit 12)。
        disable_wdt(LP_WDT_WPROTECT, LP_WDT_CONFIG0, 1 << 12);
        // TIMG0 MWDT:无 flash-boot 位,只清 wdt_en(bit 31)。
        disable_wdt(TIMG0_WDT_WPROTECT, TIMG0_WDT_CONFIG0, 0);
    }
}

crate::define_peripheral! {
    (console_uart, blueos_driver::uart::esp32_usb_serial::Esp32UsbSerial<0x6000_F000>,
     blueos_driver::uart::esp32_usb_serial::Esp32UsbSerial::<0x6000_F000>::new()),
}

crate::define_pin_states!(None);

#[inline(always)]
pub(crate) fn send_ipi(_hart: usize) {}

#[inline(always)]
pub(crate) fn clear_ipi(_hart: usize) {}

static ESP32_USB_SERIAL_ISR: Esp32UsbSerialIsr<0x6000_F000, crate::drivers::serial::Serial> =
    Esp32UsbSerialIsr::<0x6000_F000, _> {
        data: &crate::drivers::serial::TTY_SERIAL,
        tx_isr: Some(crate::drivers::serial::Serial::xmitchars),
        rx_isr: Some(crate::drivers::serial::Serial::recvchars),
    };
