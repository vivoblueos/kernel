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
use crate::arch::riscv::{local_irq_enabled, trap_entry, Context, MIE_MEIE};
use blueos_driver::uart::esp32_usb_serial::Esp32UsbSerialIsr;
use blueos_hal::{isr::IsrDesc, Has8bitDataReg};

// ESP32-C6 systimer. C6 runs the systimer off the 40MHz XTAL divided down to
// 16MHz (same as C3); the period math in the driver is driven by HZ, so we keep
// 16MHz here. Base 0x6000_A000 per the C6 TRM.
// FIXME: Only support unit0 for now
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

/// PLIC_MX base for ESP32-C6 (`DR_REG_PLIC_MX_BASE` @ 0x2000_1000)。C6 的
/// HP-CPU 外部中断控制器是 per-CPU-line PLIC_MX(不是 SiFive PLIC,也不是 C3
/// 的 INTPRI 风格 INTMUX)。实测已确认:INTMTX 路由的 USB/systimer 中断源
/// pending 出现在 PLIC_MX 的 EIP_STATUS(+0xC),而非遗留 INTPRI 块(0x600C_5000,
/// 其 EIP 恒 0)——故 esp-idf 用 PLIC_MX 是对的,BlueOS 也配 PLIC_MX。
/// 布局(esp-idf soc/esp32c6/register/soc/plic_reg.h):
///   ENABLE      @ +0x0  (bit per CPU line)
///   TYPE        @ +0x4  (0=level/1=edge, 默认 0=level)
///   CLEAR       @ +0x8  (write-1-to-clear per line)
///   EMIP_STATUS @ +0xC  (RO,bit[n]=line n 有 pending)
///   PRI[n]      @ +0x10 + n*4 (4-bit [3:0])
///   THRESH      @ +0x90 ([7:0])
/// dispatch 模型同 C3:mcause 低字节=CPU 线号,ISR 清各自外设源,
/// level 型线在源清除后自动去断言。
const PLIC_MX_BASE: usize = 0x2000_1000;
const PLIC_MX_ENABLE: usize = PLIC_MX_BASE + 0x0;
const PLIC_MX_PRI: usize = PLIC_MX_BASE + 0x10; // PRI[line] @ PRI + line*4
const PLIC_MX_THRESH: usize = PLIC_MX_BASE + 0x90;
// EMIP_STATUS:外部中断 pending 位图,RO。bit[n]=line n 有 pending。
const PLIC_MX_EMIP_STATUS: usize = PLIC_MX_BASE + 0xC;

/// INTERRUPT_MATRIX base (`DR_REG_INTERRUPT_MATRIX_BASE`). This is the
/// source→CPU-line router. Each peripheral source has a dedicated `_MAP` register
/// whose 5-bit field [4:0] selects which CPU line (0..31) the source is routed
/// to. The register offsets are NOT contiguous (there are gaps), so each map is
/// programmed by its absolute offset. Source IDs (from esp-idf
/// `soc/esp32c6/include/soc/interrupts.h`) only matter for reading the
/// `INT_STATUS` bitmap to identify a source; routing itself uses the MAP
/// register address. C3 does this routing inside `Esp32Intc::allocate_irq` via
/// its INTPRI layout; C6 cannot reuse `Esp32Intc` (different layout), so we do
/// it with raw register writes here.
const INTMTX_BASE: usize = 0x6001_0000;
// USB_SERIAL_JTAG source → CPU line (esp-idf INTMTX_CORE0_USB_INTR_MAP_REG @ +0xc0)
const INTMTX_USB_SERIAL_JTAG_MAP: usize = INTMTX_BASE + 0xc0;
// SYSTIMER_TARGET0 source → CPU line (esp-idf INTMTX_CORE0_SYSTIMER_TARGET0_INTR_MAP_REG @ +0xe4)
const INTMTX_SYSTIMER_TARGET0_MAP: usize = INTMTX_BASE + 0xe4;

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

/// CPU interrupt line numbers. ESP32-C6 puts the CPU line number (NOT RISC-V
/// cause 11) into `mcause` for external interrupts, so trap.rs's
/// `#[cfg(not(has_plic))]` branch hands `mcause` to `handle_intc_irq` and we
/// match on `mcause & 0xff`. We reuse C3's line assignment (USB→15,
/// systimer→16) purely for familiarity; any free lines would work. Lines 0/1 are
/// reserved for WiFi on C3 and unused here (CONFIG_ENABLE_NET=n).
const USB_SERIAL_JTAG_INT_NUM: usize = 15;
const SYSTIMER_TARGET0_INT_NUM: usize = 16;

#[inline]
unsafe fn write32(addr: usize, val: u32) {
    unsafe { core::ptr::write_volatile(addr as *mut u32, val) };
}

#[inline]
unsafe fn read32(addr: usize) -> u32 {
    unsafe { core::ptr::read_volatile(addr as *const u32) }
}

/// Route a peripheral source to a CPU line in the INTERRUPT_MATRIX, then enable
/// that line in PLIC_MX at the given priority. `map_reg` is the source's MAP
/// register offset (NOT source_id*4).
unsafe fn route_source(map_reg: usize, line: usize, prio: u32) {
    unsafe {
        // [4:0] = target CPU line
        write32(map_reg, line as u32);
        // PLIC_MX priority for this line (4-bit field, 0xF max)
        write32(PLIC_MX_PRI + line * 4, prio & 0xF);
        // enable the line (set its bit in the 32-line ENABLE bitmap)
        let en = read32(PLIC_MX_ENABLE);
        write32(PLIC_MX_ENABLE, en | (1u32 << line));
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

/// External interrupt handler — routed here via trap.rs `#[cfg(not(has_plic))]`.
/// Dispatches on the CPU line number carried in `mcause` (same model as C3).
pub(crate) fn handle_intc_irq(ctx: &Context, mcause: usize, mtval: usize) {
    let _ = (ctx, mtval);
    // [DIAG] confirm dispatch match. Remove after.
    let low = mcause & 0xff;
    crate::kearly_println!("[DIAG] handle_intc_irq low={} (usb=15 sys=16)", low);
    match low {
        SYSTIMER_TARGET0_INT_NUM => {
            ClockImpl::clear_interrupt();
            crate::time::handle_clock_interrupt();
        }
        USB_SERIAL_JTAG_INT_NUM => {
            ESP32_USB_SERIAL_ISR.service_isr();
        }
        _ => {}
    }
}

/// 外设 INT_RAW/INT_ST/INT_ENA 基址（USB-Serial-JTAG @ 0x6000_F000）。
/// 用于 dump：判断 USB RX 中断源是否已 arm、是否有 pending 未清。
const USB_SERIAL_JTAG_BASE: usize = 0x6000_F000;
const USB_INT_RAW: usize = USB_SERIAL_JTAG_BASE + 0x08;
const USB_INT_ST: usize = USB_SERIAL_JTAG_BASE + 0x0c;
const USB_INT_ENA: usize = USB_SERIAL_JTAG_BASE + 0x10;
/// USB_SERIAL_JTAG_INT_ENA 位定义：bit2=SERIAL_OUT_RECV_PKT(RX), bit3=SERIAL_IN_EMPTY(TX)
const USB_RX_INT_BIT: u32 = 1 << 2;

/// systimer 寄存器（@ 0x6000_A000），用于 dump。
const SYSTIMER_BASE: usize = 0x6000_A000;
const SYSTIMER_CONF: usize = SYSTIMER_BASE + 0x00; // bit31=CLK_EN,bit24=TARGET0_WORK_EN
const SYSTIMER_INT_ENA: usize = SYSTIMER_BASE + 0x64; // bit0=TARGET0
const SYSTIMER_INT_RAW: usize = SYSTIMER_BASE + 0x68;
const SYSTIMER_TARGET0_CONF: usize = SYSTIMER_BASE + 0x34;

/// INTMTX 时钟门控寄存器。bit0=REG_CLK_EN，默认 1；若被关则所有 MAP 写失效。
const INTMTX_CLOCK_GATE: usize = INTMTX_BASE + 0x140;

/// 运行时 dump：打印中断 delivery 链上每一个 gate 的实测值。
/// 在 board init() 末尾、shell 阻塞前调用，定位"静态配置全开但无中断 trap"的根因。
#[allow(dead_code)]
unsafe fn dump_intc_state() {
    unsafe {
        // ---- CSR 级（CPU 侧门控）----
        let mie: usize;
        let mstatus: usize;
        let mtvec: usize;
        core::arch::asm!(
            "csrr {mie}, mie",
            "csrr {mstatus}, mstatus",
            "csrr {mtvec}, mtvec",
            mie = out(reg) mie,
            mstatus = out(reg) mstatus,
            mtvec = out(reg) mtvec,
            options(nostack, preserves_flags),
        );
        crate::kearly_println!("[DIAG] === C6 INTC dump ===");
        crate::kearly_println!("[DIAG] mie      =0x{:08x} (bit11=MEIE expect 1)", mie);
        crate::kearly_println!("[DIAG] mstatus  =0x{:08x} (bit3=MIE; 0 here=ok, set by schedule)", mstatus);
        crate::kearly_println!("[DIAG] mtvec    =0x{:08x} (bit0=1 vectored, base=_vector_table)", mtvec);

        // ---- PLIC_MX（CPU line 侧 enable/prio/thresh/pending）----
        let en = read32(PLIC_MX_ENABLE);
        // TYPE @ +0x4:bit15=USB line,0=level(默认)/1=edge。从未实测过,加进 dump
        // 排除 edge/level 嫌疑(C3 也不写 TYPE 且工作,默认 level 应正确)。
        let ptype = read32(PLIC_MX_BASE + 0x4);
        let pri15 = read32(PLIC_MX_PRI + 15 * 4);
        let pri16 = read32(PLIC_MX_PRI + 16 * 4);
        let thresh = read32(PLIC_MX_THRESH);
        let emip = read32(PLIC_MX_EMIP_STATUS);
        crate::kearly_println!("[DIAG] PLIC ENABLE =0x{:08x} (bit15/16 expect set)", en);
        crate::kearly_println!("[DIAG] PLIC TYPE   =0x{:08x} (bit15=usb 0=level)", ptype);
        crate::kearly_println!("[DIAG] PLIC PRI15  =0x{:x} PRI16=0x{:x} (expect 1)", pri15 & 0xF, pri16 & 0xF);
        crate::kearly_println!("[DIAG] PLIC THRESH =0x{:x} (expect 0)", thresh & 0xFF);
        crate::kearly_println!("[DIAG] PLIC EMIP    =0x{:08x} (bit15=usb pend, bit16=sys pend)", emip);

        // ---- INTMTX（源→line 路由 + 时钟门控）----
        let usb_map = read32(INTMTX_USB_SERIAL_JTAG_MAP) & 0x1F;
        let sys_map = read32(INTMTX_SYSTIMER_TARGET0_MAP) & 0x1F;
        let clk_gate = read32(INTMTX_CLOCK_GATE) & 0x1;
        crate::kearly_println!("[DIAG] INTMTX usb_map  ={} (expect 15)", usb_map);
        crate::kearly_println!("[DIAG] INTMTX sys_map  ={} (expect 16)", sys_map);
        crate::kearly_println!("[DIAG] INTMTX clk_gate ={} (expect 1)", clk_gate);

        // ---- USB-Serial-JTAG 源侧 ----
        let u_raw = read32(USB_INT_RAW);
        let u_st = read32(USB_INT_ST);
        let u_ena = read32(USB_INT_ENA);
        crate::kearly_println!("[DIAG] USB INT_ENA =0x{:08x} (bit2=RX expect 1)", u_ena);
        crate::kearly_println!("[DIAG] USB INT_RAW =0x{:08x} (bit2=RX pending)", u_raw);
        crate::kearly_println!("[DIAG] USB INT_ST  =0x{:08x}", u_st);

        // ---- systimer 源侧 ----
        let s_conf = read32(SYSTIMER_CONF);
        let s_ena = read32(SYSTIMER_INT_ENA);
        let s_raw = read32(SYSTIMER_INT_RAW);
        let s_tconf = read32(SYSTIMER_TARGET0_CONF);
        crate::kearly_println!("[DIAG] SYS CONF    =0x{:08x} (bit31=clk,bit24=tgt0_en)", s_conf);
        crate::kearly_println!("[DIAG] SYS INT_ENA =0x{:x} (bit0=tgt0 expect 1)", s_ena & 0x7);
        crate::kearly_println!("[DIAG] SYS INT_RAW =0x{:x} (bit0=tgt0 pending)", s_raw & 0x7);
        crate::kearly_println!("[DIAG] SYS TGT0CONF=0x{:08x}", s_tconf);
        crate::kearly_println!("[DIAG] === end dump ===");
    }
}

/// EP1_CONF 寄存器(@ +0x04),bit2=OUT_EP_DATA_AVAIL(主机有数据可读)。
/// 用于 idle hook 诊断:主动 poll RX 数据是否到达外设。
const USB_EP1_CONF: usize = USB_SERIAL_JTAG_BASE + 0x04;
/// EP1 数据寄存器(@ +0x00),读它取出一个 RX 字节。
const USB_EP1_REG: usize = USB_SERIAL_JTAG_BASE + 0x00;

/// [DIAG] 诊断 idle hook:shell 阻塞期间被反复调用。每次读 USB RX 中断源
/// (INT_RAW bit2)、PLIC pending(EMIP bit15)、并主动 poll RX FIFO。目的:
/// 定位按键瞬间中断到底卡在哪一级。只在状态变化时打印,避免刷屏。
/// 确认后随 set_idle_hook 调用一起移除。
static DIAG_LAST_RX: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(usize::MAX);
static DIAG_IDLE_TICK: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);

extern "C" fn diag_idle_poll() {
    let n = DIAG_IDLE_TICK.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
    unsafe {
        // [DIAG] 心跳:每 100000 次无条件打印一次,证明 idle hook 确实在跑。
        // 若这行永远不出现,说明 idle 线程根本没执行(schedule 没到 idle loop,
        // 或 shell 没真正阻塞让出 CPU)。确认后移除。
        if n % 100000 == 0 {
            let mie: usize;
            let mstatus: usize;
            let mip: usize;
            core::arch::asm!(
                "csrr {mie}, mie",
                "csrr {mstatus}, mstatus",
                "csrr {mip}, mip",
                mie = out(reg) mie,
                mstatus = out(reg) mstatus,
                mip = out(reg) mip,
                options(nostack, preserves_flags),
            );
            // mip bit11=MEIP(外部中断 pending 到 CPU 的真实电平)。
            // 若 emip(PLIC 内部)=1 但 mip.MEIP=0,说明 PLIC pending 没变成 meip。
            crate::kearly_println!(
                "[DIAG] idle heartbeat #{} mie=0x{:x} mstatus=0x{:x} mip=0x{:x}(meip={})",
                n,
                mie,
                mstatus,
                mip,
                (mip >> 11) & 1
            );
        }
        let u_raw = read32(USB_INT_RAW);
        let u_st = read32(USB_INT_ST);
        let emip = read32(PLIC_MX_EMIP_STATUS);
        let rx_pend = ((u_raw >> 2) & 1) as usize;
        let emip_usb = ((emip >> 15) & 1) as usize;
        // 主动 poll:OUT_EP_DATA_AVAIL(bit2 of EP1_CONF)表示主机 OUT 包有数据。
        let avail = ((read32(USB_EP1_CONF) >> 2) & 1) as usize;
        // 状态三元组打包成一个 usize:rx | emip<<1 | avail<<2
        let snap = rx_pend | (emip_usb << 1) | (avail << 2);
        let prev = DIAG_LAST_RX.swap(snap, core::sync::atomic::Ordering::Relaxed);
        // 仅在状态变化时打印,避免刷屏。
        if prev != snap {
            crate::kearly_println!(
                "[DIAG] idle#{} CHG rx_raw={} int_st={} emip_usb={} fifo_avail={}",
                n,
                rx_pend,
                u_st & 0x4,
                emip_usb,
                avail
            );
        }
        // 若 FIFO 有数据但中断没触发,主动读出来看是不是有效字符。
        if avail == 1 {
            let b = read32(USB_EP1_REG) & 0xff;
            crate::kearly_println!("[DIAG] idle polled byte=0x{:02x}", b);
        }
    }
}

pub(crate) fn init() {
    assert!(!local_irq_enabled());

    crate::boot::init_runtime();
    crate::boot::init_heap();
    init_vector_table();

    blueos_driver::systimer::esp32_sys_timer::Esp32SysTimer::<0x6000_A000, 16_000_000>::init();

    // Configure the two interrupts we use. C6 has neither C3's INTMUX nor a
    // SiFive PLIC: routing is done in the INTERRUPT_MATRIX (source→CPU line) and
    // enable/priority/threshold in PLIC_MX. `route_source` does both. There is
    // no claim/complete pair to drive — ISRs clear their own peripheral
    // interrupt and the level-typed PLIC_MX line auto-deasserts.
    unsafe {
        // 完全照搬 C3 数值(seeed_xiao_esp32c3 set_threshold(1)+set_priority(15)):
        // threshold=1、priority=15。priority 4 位字段存得下 0xF,1>0/15>1 都满足
        // 递交条件。这是与 C3 通路的逐行对照基准,排除数值差异干扰。
        write32(PLIC_MX_THRESH, 1);
        route_source(INTMTX_USB_SERIAL_JTAG_MAP, USB_SERIAL_JTAG_INT_NUM, 15);
        route_source(INTMTX_SYSTIMER_TARGET0_MAP, SYSTIMER_TARGET0_INT_NUM, 15);

        // PLIC_MX's external-interrupt output is standard RISC-V `meip`, gated by
        // `mie.MEIE` (bit 11). bootstrap() does write `csrs mie, MEIE|MSIE|MTIE`,
        // but that statement is gated behind `#[cfg(has_mie)]` and `has_mie` is
        // never defined anywhere in the repo, so it is dead code — the OS never
        // touches `mie`. C6 ROM resets `mie` to 0 (per RISC-V spec), so without
        // an explicit set here NO external interrupt (USB RX on line 15, systimer
        // on line 16) can reach the trap handler. C3's custom INTC (INTPRI/INTMUX)
        // bypasses the `mie.MEIE` gate, which is why C3 works without this — C6's
        // PLIC_MX does not. Safe here: `mstatus.MIE` is still clear (asserted
        // above), so writing `mie` now can't take interrupts until we later flip
        // `mstatus.MIE`.
        core::arch::asm!(
            "csrs mie, {mie}",
            mie = in(reg) MIE_MEIE,
            options(nostack, preserves_flags),
        );
    }

    // Disable both flash-boot watchdogs the bootloader left running (LP_WDT
    // RTC watchdog + TIMG0 MWDT). Without this the chip resets a few hundred
    // ms after the app starts, killing the host serial monitor with a
    // `Broken pipe`. See the LP_WDT/TIMG0 constants above for addresses.
    // NOTE: WiFi/power-domain init is intentionally omitted — CONFIG_ENABLE_NET=n
    // for this board, so there is no radio to bring up.
    unsafe {
        // LP_WDT: also clear wdt_flashboot_mod_en (bit 12).
        disable_wdt(LP_WDT_WPROTECT, LP_WDT_CONFIG0, 1 << 12);
        // TIMG0 MWDT: no flash-boot bit, just wdt_en (bit 31).
        disable_wdt(TIMG0_WDT_WPROTECT, TIMG0_WDT_CONFIG0, 0);

        // [DIAG] dump 中断 delivery 链上每个 gate 的运行时实测值,
        // 定位“静态配置全开但无外部中断 trap”的根因。确认后移除。
        dump_intc_state();

        // [DIAG] 注入诊断 idle hook:shell 阻塞期间轮询 USB RX/PLIC pending,
        // 抓按键瞬间的中断状态。确认后移除(改回默认 wfi)。
        crate::scheduler::set_idle_hook(diag_idle_poll);
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
