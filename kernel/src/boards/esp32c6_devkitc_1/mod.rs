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
// board::init() 跑在 logger::logger_init()(boot.rs:145)和 console UART configure
// (boot.rs:99)之前,故 log::info! 是 no-op、kprintln 走未 configure 的 console。
// kearly_println! 的 EarlyConsole 直接写 USB Serial JTAG 寄存器(boot ROM 已配好),
// 是早期诊断唯一可用通道。
use crate::kearly_println;
use blueos_driver::uart::esp32_usb_serial::Esp32UsbSerialIsr;
use blueos_hal::{isr::IsrDesc, Has8bitDataReg};

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

const PLIC_MX_BASE: usize = 0x2000_1000;
const PLIC_MX_ENABLE: usize = PLIC_MX_BASE;  // enable 寄存器 @ 基址 +0x0
const PLIC_MX_TYPE: usize = PLIC_MX_BASE + 0x4;
const PLIC_MX_CLEAR: usize = PLIC_MX_BASE + 0x8;
const PLIC_MX_EIP_STATUS: usize = PLIC_MX_BASE + 0xC;
const PLIC_MX_PRI: usize = PLIC_MX_BASE + 0x10; // PRI[line] @ PLIC_MX_PRI + line*4
const PLIC_MX_THRESH: usize = PLIC_MX_BASE + 0x90;

const MIDELEG_UEXT_BIT: usize = 1 << 8;
const MIDELEG_UTIMER_BIT: usize = 1 << 4;
const MIDELEG_USOFT_BIT: usize = 1 << 0;
/// 一次性清零 mideleg 复位值 0x111 的三个委托位(bit0|bit4|bit8)。
const MIDELEG_DELEG_MASK: usize = MIDELEG_USOFT_BIT | MIDELEG_UTIMER_BIT | MIDELEG_UEXT_BIT;

const INTMTX_BASE: usize = 0x6001_0000;

const INTMTX_USB_SERIAL_JTAG_MAP: usize = INTMTX_BASE + 0xC0;

const INTMTX_SYSTIMER_TARGET0_MAP: usize = INTMTX_BASE + 0xE4;

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
const LP_WDT_CONFIG0: usize = LP_WDT_BASE;  // wdtconfig0 @ +0x00
const LP_WDT_WPROTECT: usize = LP_WDT_BASE + 0x18;
const TIMG0_BASE: usize = 0x6000_8000;
const TIMG0_WDT_CONFIG0: usize = TIMG0_BASE + 0x48;
const TIMG0_WDT_WPROTECT: usize = TIMG0_BASE + 0x64;
const WDT_WKEY: u32 = 0x50D8_3AA1;

const WDT_EN_BIT: u32 = 1 << 31; 
                                 
const WDT_FLASHBOOT_MOD_EN_BIT: u32 = 1 << 12; // bit 12

const USB_SERIAL_JTAG_INT_NUM: usize = 15;

#[inline]
unsafe fn write32(addr: usize, val: u32) {
    unsafe { core::ptr::write_volatile(addr as *mut u32, val) };
}

#[inline]
unsafe fn read32(addr: usize) -> u32 {
    unsafe { core::ptr::read_volatile(addr as *const u32) }
}

unsafe fn route_source(map_reg: usize, line: usize, prio: u32) {
    unsafe {
        let mut mie: usize;
        core::arch::asm!(
            "csrr {mie}, mie",
            "csrw mie, zero",
            mie = out(reg) mie,
            options(nostack, preserves_flags),
        );
        write32(map_reg, line as u32);
        let t = read32(PLIC_MX_TYPE);
        write32(PLIC_MX_TYPE, t & !(1u32 << line));
        write32(PLIC_MX_PRI + line * 4, prio & 0xF);
        let en = read32(PLIC_MX_ENABLE);
        write32(PLIC_MX_ENABLE, en | (1u32 << line));
        mie |= 1usize << line;
        core::arch::asm!("fence io, io", options(nostack, preserves_flags));
        core::arch::asm!(
            "csrw mie, {mie}",
            mie = in(reg) mie,
            options(nostack, preserves_flags),
        );
    }
}

#[inline]
unsafe fn disable_wdt(wprotect: usize, config0: usize, flashboot_mask: u32) {
    unsafe {
        write32(wprotect, WDT_WKEY); // unlock
        let cfg = read32(config0);
        write32(config0, cfg & !(WDT_EN_BIT | flashboot_mask));
        write32(wprotect, 0); // re-lock
    }
}

// ===================================================================
// Ana I2C master 协议 + BBPLL 自校准 + regi2c ENIF
//
// 背景:BlueOS 绕过 IDF 系统初始化(esp_rtc_init / pmu_init),两件事从没做:
//   缺口 1 — BBPLL regi2c 自校准(rtc_clk.c:155 rtc_clk_bbpll_configure 五步)
//   缺口 2 — regi2c ENIF 四位(pmu_init.c:214-217 的 4 个 REGI2C_WRITE_MASK)
// 两者都要走 ana i2c master 寄存器访问 analog slave(BBPLL=0x66 / DIG_REG=0x6D)。
// C6 ROM 不导出 esp_rom_regi2c_write(_mask) 符号(esp32c6.rom.api.ld 无,phy.ld
// 仅 rom_i2c_enter/exit_critical),故 FFI 不可行,必须在此裸写 i2c 协议。
//
// 协议移植自 esp-idf patches/esp_rom_regi2c_esp32h2.c(C6/H2 共享),寄存器
// 地址/字段位号逐个核实自 components/soc/esp32c6/register/soc/i2c_ana_mst_reg.h
// 与 components/soc/esp32c6/include/soc/regi2c_defs.h:
//   DR_REG_I2C_ANA_MST_BASE = 0x600AF800 (reg_base.h:58)
//   I2C_ANA_MST_I2C0_CTRL_REG    @ +0x00 → 0x600AF800
//     bit[7:0]   SLAVE_ID    (block id,如 0x66=BBPLL / 0x6D=DIG_REG)
//     bit[15:8]  ADDR        (slave 内 8-bit reg offset)
//     bit[23:16] DATA        (写时为写入值,读时为读出值)
//     bit24      WR_CNTL     (0=read, 1=write)
//     bit25      BUSY        (RO,1=传输进行中,轮询至 0)
//   I2C_MST_ANA_CONF0_REG  @ +0x18 → 0x600AF818
//     bit2  BBPLL_STOP_FORCE_HIGH  (置 1 停止校准,拉高 stop)
//     bit3  BBPLL_STOP_FORCE_LOW   (置 1 启动校准,拉低 stop)
//     bit24 BBPLL_CAL_DONE         (RO,1=校准完成)
//   I2C_MST_ANA_CONF1_REG  @ +0x1C → 0x600AF81C (R/W,24-bit slave RD mask)
//   I2C_MST_ANA_CONF2_REG  @ +0x20 → 0x600AF820 (R/W,24-bit slave MST_SEL)
//     bit9  BBPLL_MST_SEL
//     bit12 DIG_REG_MST_SEL
//   i2c_sel 语义(见 esp_rom_hp_regi2c_esp32c6.c:115 `return i2c_sel ? 0 : 1`):
//   MST_SEL 位非0 → 用 I2C0(+0x00);MST_SEL 位=0 → 用 I2C1(+0x04)。
//   CONF2 复位值=0x0004(仅 bit2),BBPLL_MST_SEL(bit9)/DIG_REG_MST_SEL(bit12)
//   复位皆 0 → default 走 I2C1。这是反直觉但确凿的硬件路由:MST_SEL=1 选 I2C0,
//   MST_SEL=0 选 I2C1。之前写反过(误以为 1=I2C1),致 ENIF readback 全 0xff。
//   CONF1 的 RD_MASK:写 CONF1 = (~对应 RD bit) & 0xFFFFFF,作用是关断其他
//   analog slave 的读通路,只留目标 slave。
//   MODEM_LPCON.clk_conf.clk_i2c_mst_en(bit2)开 ana i2c master 时钟门控
//   (regi2c_ctrl_ll_master_enable_clock;esp-phy enable_phy 也会开,但校准
//   发生在 PHY enable 之前,故此处自己再置一次保证可用)。
// ===================================================================

// Ana I2C master register block base (DR_REG_I2C_ANA_MST_BASE)
const I2C_ANA_MST_BASE: usize = 0x600A_F800;
const I2C_ANA_MST_I2C0_CTRL: usize = I2C_ANA_MST_BASE; // +0x00
const I2C_ANA_MST_I2C1_CTRL: usize = I2C_ANA_MST_BASE + 0x04;
const I2C_MST_ANA_CONF0: usize = I2C_ANA_MST_BASE + 0x18; // BBPLL 校准控制
const I2C_MST_ANA_CONF1: usize = I2C_ANA_MST_BASE + 0x1C; // slave RD mask
const I2C_MST_ANA_CONF2: usize = I2C_ANA_MST_BASE + 0x20; // slave MST_SEL

// MODEM_LPCON.clk_conf @ 0x600A_F018,bit2 = clk_i2c_mst_en(ana i2c master 时钟)
const MODEM_LPCON_CLK_CONF_FOR_I2C: usize = 0x600A_F018;
const CLK_I2C_MST_EN_BIT: u32 = 1 << 2;

// BBPLL calibration control bits in I2C_MST_ANA_CONF0
const BBPLL_STOP_FORCE_HIGH: u32 = 1 << 2; // bit2: set to stop calibration (stop=high)
const BBPLL_STOP_FORCE_LOW: u32 = 1 << 3; // bit3: set to start calibration (stop=low)
const BBPLL_CAL_DONE: u32 = 1 << 24; // bit24 (RO): 1 = calibration done

// I2C_CTRL field layout (I2C_ANA_MST_I2C0/1_CTRL)
const REGI2C_RTC_SLAVE_ID_S: u32 = 0;
const REGI2C_RTC_ADDR_S: u32 = 8;
const REGI2C_RTC_DATA_S: u32 = 16;
const REGI2C_RTC_WR_CNTL: u32 = 1 << 24; // bit24: 0=read, 1=write
const REGI2C_RTC_BUSY: u32 = 1 << 25; // bit25 (RO): 1=busy

// Ana I2C slave block ids (regi2c_defs.h / patches esp_rom_regi2c_esp32h2.c)
const REGI2C_BBPLL: u8 = 0x66;
const REGI2C_DIG_REG: u8 = 0x6D; // = I2C_DIG_REG, ENIF 四位的目标 slave

// Slave select masks for I2C_MST_ANA_CONF1 (RD_MASK: clear target bit, keep others)
// CONF1 bit6=BIAS / bit7=BBPLL / bit8=ULP / bit9=SAR / bit10=DIG_REG
const REGI2C_BBPLL_RD_MASK: u32 = !(1 << 7) & 0x00FF_FFFF;
const REGI2C_DIG_REG_RD_MASK: u32 = !(1 << 10) & 0x00FF_FFFF;
// Slave select bits for I2C_MST_ANA_CONF2 (MST_SEL: 1=route to I2C1)
const REGI2C_BBPLL_MST_SEL: u32 = 1 << 9;
const REGI2C_DIG_REG_MST_SEL: u32 = 1 << 12;

// ROM ets_delay_us 绝对地址 = 0x40000040(esp32c6.rom.ld:31 强符号定义)。
// link.x 不 INCLUDE esp32c6.rom.ld,故不能 extern 引符号(会 undefined reference);
// 这里用裸地址函数指针直接调用,绕过链接器符号解析。函数签名 void ets_delay_us(uint32_t us),
// RISC-V calling convention: a0 = us。
const ETS_DELAY_US: usize = 0x4000_0040;
#[inline]
unsafe fn ets_delay_us(us: u32) {
    let f: unsafe extern "C" fn(u32) = core::mem::transmute(ETS_DELAY_US);
    unsafe { f(us) };
}

/// Enable the ana I2C master clock + select target slave, return which I2C
/// controller (0 or 1) to use for the transfer. Mirrors regi2c_enable_block()
/// in patches/esp_rom_regi2c_esp32h2.c.
#[inline]
unsafe fn regi2c_enable_block(block: u8) -> u8 {
    // Enable ana I2C master clock gate (MODEM_LPCON.clk_conf.bit2).
    let v = read32(MODEM_LPCON_CLK_CONF_FOR_I2C);
    write32(MODEM_LPCON_CLK_CONF_FOR_I2C, v | CLK_I2C_MST_EN_BIT);

    // Pick the I2C controller based on CONF2 MST_SEL bit for this slave,
    // and write CONF1 RD_MASK so only the target slave's read path is live.
    // NOTE: esp-idf semantics (esp_rom_hp_regi2c_esp32c6.c:115) are inverted:
    //   MST_SEL bit set   → use I2C0  (i2c_sel = 0)
    //   MST_SEL bit clear → use I2C1  (i2c_sel = 1)
    // CONF2 reset = 0x0004 (bit2 only), so BBPLL/DIG_REG MST_SEL bits reset to 0
    // → default routes through I2C1. Earlier this was inverted, causing every
    // regi2c read/write to hit the wrong controller and read back 0xff.
    let (mst_sel_bit, rd_mask): (u32, u32) = match block {
        REGI2C_BBPLL => (REGI2C_BBPLL_MST_SEL, REGI2C_BBPLL_RD_MASK),
        REGI2C_DIG_REG => (REGI2C_DIG_REG_MST_SEL, REGI2C_DIG_REG_RD_MASK),
        _ => (0, 0x00FF_FFFF),
    };
    let i2c_sel = if (read32(I2C_MST_ANA_CONF2) & mst_sel_bit) != 0 {
        0
    } else {
        1
    };
    write32(I2C_MST_ANA_CONF1, rd_mask);
    i2c_sel
}

/// Wait for the ana I2C controller to finish (BUSY=0). Bounded loop to avoid
/// hanging the whole boot if the analog bus is wedged.
#[inline]
unsafe fn regi2c_wait_idle(ctrl_reg: usize) {
    for _ in 0..100_000 {
        if (read32(ctrl_reg) & REGI2C_RTC_BUSY) == 0 {
            return;
        }
    }
    // Timeout: ana I2C never went idle. Log and bail rather than hang.
    kearly_println!("[bbpll] ana i2c busy timeout (ctrl=0x{:x})", read32(ctrl_reg));
}

/// Read one 8-bit register from an ana I2C slave. Mirrors regi2c_read_impl().
#[inline]
unsafe fn regi2c_read(block: u8, reg_add: u8) -> u8 {
    let i2c_sel = regi2c_enable_block(block);
    let ctrl = if i2c_sel == 1 {
        I2C_ANA_MST_I2C1_CTRL
    } else {
        I2C_ANA_MST_I2C0_CTRL
    };
    regi2c_wait_idle(ctrl);
    // Read transaction: slave_id[7:0] | addr[15:8], WR_CNTL=0
    let temp = ((block as u32) << REGI2C_RTC_SLAVE_ID_S)
        | ((reg_add as u32) << REGI2C_RTC_ADDR_S);
    write32(ctrl, temp);
    regi2c_wait_idle(ctrl);
    // DATA field is bits[23:16] of the same CTRL reg after read completes
    ((read32(ctrl) >> REGI2C_RTC_DATA_S) & 0xFF) as u8
}

/// Read-modify-write one bitfield on an ana I2C slave register.
/// Mirrors regi2c_write_mask_impl(): read current byte, clear [msb:lsb],
/// insert data, write back. data is masked to the field width.
#[inline]
unsafe fn regi2c_write_mask(block: u8, reg_add: u8, msb: u8, lsb: u8, data: u8) {
    let i2c_sel = regi2c_enable_block(block);
    let ctrl = if i2c_sel == 1 {
        I2C_ANA_MST_I2C1_CTRL
    } else {
        I2C_ANA_MST_I2C0_CTRL
    };
    // Read current value
    regi2c_wait_idle(ctrl);
    let mut temp = ((block as u32) << REGI2C_RTC_SLAVE_ID_S)
        | ((reg_add as u32) << REGI2C_RTC_ADDR_S);
    write32(ctrl, temp);
    regi2c_wait_idle(ctrl);
    let cur: u32 = (read32(ctrl) >> REGI2C_RTC_DATA_S) & 0xFF;
    // Build field mask [msb:lsb] with u32 arithmetic (u8 shift would panic
    // in debug when field_width == 8). clear_mask zeroes the target field;
    // then insert masked data into it.
    let field_width = (msb - lsb + 1) as u32;
    let field_one: u32 = (1u32 << field_width) - 1; // field_width 1-bits
    let clear_mask: u32 = !(field_one << lsb as u32) & 0xFF;
    let new_val: u32 = (cur & clear_mask) | (((data as u32) & field_one) << lsb as u32);
    // Write back: slave_id | addr | WR_CNTL=1 | data
    temp = ((block as u32) << REGI2C_RTC_SLAVE_ID_S)
        | ((reg_add as u32) << REGI2C_RTC_ADDR_S)
        | REGI2C_RTC_WR_CNTL
        | (new_val << REGI2C_RTC_DATA_S);
    write32(ctrl, temp);
    regi2c_wait_idle(ctrl);
}

/// Write one full 8-bit register on an ana I2C slave (no RMW). Mirrors
/// regi2c_write_impl(). Used for BBPLL OC_* config registers.
#[inline]
unsafe fn regi2c_write(block: u8, reg_add: u8, data: u8) {
    let i2c_sel = regi2c_enable_block(block);
    let ctrl = if i2c_sel == 1 {
        I2C_ANA_MST_I2C1_CTRL
    } else {
        I2C_ANA_MST_I2C0_CTRL
    };
    regi2c_wait_idle(ctrl);
    let temp = ((block as u32) << REGI2C_RTC_SLAVE_ID_S)
        | ((reg_add as u32) << REGI2C_RTC_ADDR_S)
        | REGI2C_RTC_WR_CNTL
        | ((data as u32) << REGI2C_RTC_DATA_S);
    write32(ctrl, temp);
    regi2c_wait_idle(ctrl);
}

// BBPLL analog config register offsets on slave 0x66. These constants are the
// I2C slave register ADDRESSES — taken verbatim from the I2C_BBPLL_OC_* macros
// in components/soc/esp32c6/include/soc/regi2c_bbpll.h (the macro value IS the
// i2c reg address; multiple field macros like DR1/DR3 share one address).
//   I2C_BBPLL_OC_REF_DIV   = 0x02  (contains REF_DIV[2:0], DCHGP[6:4], ENB_FCAL[7])
//   I2C_BBPLL_OC_DIV_7_0   = 0x03  (DIV_7_0[7:0])
//   I2C_BBPLL_OC_DR1       = 0x05  (DR1[2:0])
//   I2C_BBPLL_OC_DR3       = 0x05  (DR3[6:4], same reg as DR1)
//   I2C_BBPLL_OC_DCUR      = 0x06  (DCUR[2:0], DHREF_SEL[5:4], DLREF_SEL[6])
//   I2C_BBPLL_OC_VCO_DBIAS = 0x09  (VCO_DBIAS[1:0])
// Earlier these were all wrong (0x00/0x01/0x02/0x04/0x05/0x06) — the 0x04 write
// hit ENB_VCON/TSCHGP and wedged the BBPLL I2C bus, hanging at step3d.
const I2C_BBPLL_OC_REF_DIV: u8 = 0x02;
const I2C_BBPLL_OC_DIV_7_0: u8 = 0x03;
const I2C_BBPLL_OC_DR1: u8 = 0x05;
const I2C_BBPLL_OC_DR3: u8 = 0x05;
const I2C_BBPLL_OC_DCUR: u8 = 0x06;
const I2C_BBPLL_OC_VCO_DBIAS: u8 = 0x09;
// OC_DCUR field layout (regi2c_bbpll.h + clk_tree_ll.h:323):
//   bit[6]   DLREF_SEL (LSB=6) — set to 1
//   bit[5:4] DHREF_SEL (LSB=4) — set to 3
//   bit[2:0] DCUR              — dcur=3
// → (1<<6)|(3<<4)|3 = 0x73   (was 0x4B, DHREF_SEL LSB wrongly 3)
const BBPLL_OC_DCUR_40M: u8 = (1 << 6) | (3 << 4) | 3;
// OC_REF_DIV field layout (regi2c_bbpll.h + clk_tree_ll.h:321):
//   bit[6:4] DCHGP (LSB=4) — 5
//   bit[2:0] DIV_REF       — 0
// → (5<<4)|0 = 0x50   (was 0x28, DCHGP LSB wrongly 3)
const BBPLL_OC_REF_DIV_40M: u8 = 5 << 4;
const BBPLL_OC_DIV_7_0_40M: u8 = 8;

/// BBPLL regi2c self-calibration — reproduces rtc_clk_bbpll_configure() in
/// esp-idf components/esp_hw_support/port/esp32c6/rtc_clk.c:155-171.
///
/// 五步:① 开 ana i2c master 时钟 ② 启动校准(清 bit2 / 置 bit3)③ 写 BBPLL
/// slave 的 OC_* 频率配置(480MHz@40MHz XTAL)④ 轮询 CAL_DONE(bit24)⑤ 停止
/// 校准(清 bit3 / 置 bit2)+ 10us 等待 + 关 i2c 时钟。BBPLL 是 RF 本振源,bootloader
/// 起振了但没自校准,频偏会使 RX 无法解调 802.11 帧 → scan 0 AP。
unsafe fn bbpll_calibrate() {
    // ① Enable ana I2C master clock (regi2c_ctrl_ll_master_enable_clock(true))
    let v = read32(MODEM_LPCON_CLK_CONF_FOR_I2C);
    write32(MODEM_LPCON_CLK_CONF_FOR_I2C, v | CLK_I2C_MST_EN_BIT);
    kearly_println!("[bbpll] step1 clk on");

    // ② Start BBPLL calibration: clear STOP_FORCE_HIGH(bit2), set STOP_FORCE_LOW(bit3)
    let conf0 = read32(I2C_MST_ANA_CONF0);
    write32(I2C_MST_ANA_CONF0, (conf0 & !BBPLL_STOP_FORCE_HIGH) | BBPLL_STOP_FORCE_LOW);
    kearly_println!("[bbpll] step2 cal started (conf0=0x{:x})", read32(I2C_MST_ANA_CONF0));

    // ③ Write BBPLL analog config for 480MHz @ 40MHz XTAL (clk_ll_bbpll_set_config)
    //    Order matches esp-idf: REF_DIV, DIV_7_0, DR1(RMW), DR3(RMW), DCUR, VCO_DBIAS(RMW)
    kearly_println!("[bbpll] step3a writing OC_REF_DIV");
    regi2c_write(REGI2C_BBPLL, I2C_BBPLL_OC_REF_DIV, BBPLL_OC_REF_DIV_40M);
    kearly_println!("[bbpll] step3b writing OC_DIV_7_0");
    regi2c_write(REGI2C_BBPLL, I2C_BBPLL_OC_DIV_7_0, BBPLL_OC_DIV_7_0_40M);
    kearly_println!("[bbpll] step3c writing OC_DR1");
    regi2c_write_mask(REGI2C_BBPLL, I2C_BBPLL_OC_DR1, 7, 0, 0);
    kearly_println!("[bbpll] step3d writing OC_DR3");
    regi2c_write_mask(REGI2C_BBPLL, I2C_BBPLL_OC_DR3, 7, 0, 0);
    kearly_println!("[bbpll] step3e writing OC_DCUR");
    regi2c_write(REGI2C_BBPLL, I2C_BBPLL_OC_DCUR, BBPLL_OC_DCUR_40M);
    kearly_println!("[bbpll] step3f writing OC_VCO_DBIAS");
    regi2c_write_mask(REGI2C_BBPLL, I2C_BBPLL_OC_VCO_DBIAS, 7, 0, 2);
    kearly_println!("[bbpll] step3 done");

    // ④ Wait for CAL_DONE (bit24). Bounded loop.
    // NOTE: on C6, CAL_DONE may read 1 immediately after start — could mean
    // either (a) calibration genuinely finished fast, or (b) it never truly
    // started and CAL_DONE is stuck at its default. The readback below
    // distinguishes the two: if the OC registers we just wrote read back
    // correctly, the I2C path is real and calibration ran.
    let mut done = false;
    for _ in 0..1_000_000 {
        if (read32(I2C_MST_ANA_CONF0) & BBPLL_CAL_DONE) != 0 {
            done = true;
            break;
        }
    }
    kearly_println!("[bbpll] step4 poll done={} (conf0=0x{:x})", done, read32(I2C_MST_ANA_CONF0));

    // Diagnostic: read back the six OC registers and compare against the
    // values we just wrote. This proves whether the BBPLL I2C writes actually
    // landed in the slave — i.e. whether calibration truly ran vs CAL_DONE
    // being a stuck-default false positive.
    //   REF_DIV   expect 0x50  (DCHGP=5<<4 | div_ref=0)
    //   DIV_7_0   expect 0x08
    //   DR1|DR3   expect DR1[2:0]=0 and DR3[6:4]=0 in the same byte → low
    //              nibble 0, high nibble 0 → byte 0x00 (readback may show
    //              other reserved bits set, so mask DR1 field [2:0] and
    //              DR3 field [6:4] separately)
    //   DCUR      expect 0x73  (DLREF_SEL=1<<6 | DHREF_SEL=3<<4 | dcur=3)
    //   VCO_DBIAS expect field[1:0]=2 (full byte 0x02)
    let rb_refdiv = regi2c_read(REGI2C_BBPLL, I2C_BBPLL_OC_REF_DIV);
    let rb_div7   = regi2c_read(REGI2C_BBPLL, I2C_BBPLL_OC_DIV_7_0);
    let rb_dr     = regi2c_read(REGI2C_BBPLL, I2C_BBPLL_OC_DR1); // same addr as DR3
    let rb_dcur   = regi2c_read(REGI2C_BBPLL, I2C_BBPLL_OC_DCUR);
    let rb_dbias  = regi2c_read(REGI2C_BBPLL, I2C_BBPLL_OC_VCO_DBIAS);
    kearly_println!(
        "[bbpll] readback: refdiv=0x{:02x}(exp 0x50) div7=0x{:02x}(exp 0x08) dr=0x{:02x}(exp dr1[2:0]=0 dr3[6:4]=0) dcur=0x{:02x}(exp 0x73) dbias=0x{:02x}(exp [1:0]=2)",
        rb_refdiv, rb_div7, rb_dr, rb_dcur, rb_dbias
    );

    // esp_rom_delay_us(10) — RTC hardware settle after calibration completes
    kearly_println!("[bbpll] step5 ets_delay_us(10) enter");
    unsafe { ets_delay_us(10) };
    kearly_println!("[bbpll] step5 ets_delay_us(10) exit");

    // ⑤ Stop calibration: clear STOP_FORCE_LOW(bit3), set STOP_FORCE_HIGH(bit2)
    let conf0 = read32(I2C_MST_ANA_CONF0);
    write32(
        I2C_MST_ANA_CONF0,
        (conf0 & !BBPLL_STOP_FORCE_LOW) | BBPLL_STOP_FORCE_HIGH,
    );

    // Diagnostic: report CAL_DONE state + final CONF0 value so the user can
    // confirm the calibration actually completed rather than timing out.
    let conf0_final = read32(I2C_MST_ANA_CONF0);
    kearly_println!(
        "[bbpll] calibration done={} (CAL_DONE=b{}), conf0=0x{:x} \
         (stop_hi=b{}, stop_lo=b{})",
        done,
        (conf0_final >> 24) & 1,
        conf0_final,
        (conf0_final >> 2) & 1,
        (conf0_final >> 3) & 1,
    );

    // Disable ana I2C master clock (rtc_clk_enable_i2c_ana_master_clock(false)).
    // Note: esp-phy enable_phy() re-enables it later during PHY calibration,
    // so turning it off here matches esp-idf's post-calibration state.
    let v = read32(MODEM_LPCON_CLK_CONF_FOR_I2C);
    write32(MODEM_LPCON_CLK_CONF_FOR_I2C, v & !CLK_I2C_MST_EN_BIT);
}

/// regi2c ENIF four bits — reproduces pmu_init.c:214-217 in esp-idf
/// components/esp_hw_support/port/esp32c6/pmu_init.c. Writes I2C_DIG_REG(0x6D)
/// slave to enable the digital/rtc regulator self-calibration path:
///   reg5  bit7 = 1  ENIF_RTC_DREG  (enable rtc dreg self-cal)
///   reg7  bit7 = 1  ENIF_DIG_DREG  (enable dig dreg self-cal)
///   reg13 bit2 = 0  XPD_RTC_REG    (0 = let self-cal drive rtc voltage)
///   reg13 bit3 = 0  XPD_DIG_REG    (0 = let self-cal drive dig voltage)
/// These let the on-chip regulator settle to the calibrated voltage instead of
/// the reset default, complementing the dbias set in ⑥.
unsafe fn regi2c_enif_init() {
    // reg5 bit7 = 1 (ENIF_RTC_DREG, msb=lsb=7)
    regi2c_write_mask(REGI2C_DIG_REG, 5, 7, 7, 1);
    // reg7 bit7 = 1 (ENIF_DIG_DREG, msb=lsb=7)
    regi2c_write_mask(REGI2C_DIG_REG, 7, 7, 7, 1);
    // reg13 bit2 = 0 (XPD_RTC_REG, msb=lsb=2)
    regi2c_write_mask(REGI2C_DIG_REG, 13, 2, 2, 0);
    // reg13 bit3 = 0 (XPD_DIG_REG, msb=lsb=3)
    regi2c_write_mask(REGI2C_DIG_REG, 13, 3, 3, 0);

    // Readback to confirm the four bits actually landed (analog bus could NACK).
    let r5 = regi2c_read(REGI2C_DIG_REG, 5);
    let r7 = regi2c_read(REGI2C_DIG_REG, 7);
    let r13 = regi2c_read(REGI2C_DIG_REG, 13);
    kearly_println!(
        "[enif] dig_reg readback: reg5=0x{:02x}(enif_rtc=b{}) \
         reg7=0x{:02x}(enif_dig=b{}) reg13=0x{:02x}(xpd_rtc=b{}, xpd_dig=b{})",
        r5,
        (r5 >> 7) & 1,
        r7,
        (r7 >> 7) & 1,
        r13,
        (r13 >> 2) & 1,
        (r13 >> 3) & 1,
    );
}

pub(crate) fn handle_intc_irq(ctx: &Context, mcause: usize, mtval: usize) {
    let _ = (ctx, mtval);
    match mcause & 0xff {
        // WiFi 中断:libnet80211 把 WIFI_MAC/WIFI_PWR 源聚合到 CPU intr 1
        // (见 esp32_wlan::api::set_isr 的 ISR_INTERRUPT_1),trap 进来后由此分发。
        // 与 C3 板级 seeed_xiao_esp32c3/mod.rs:97-100 同构。
        0 | 1 => {
            #[cfg(enable_net)]
            crate::net::link::esp32_wlan::api::ISR_INTERRUPT_1.dispatch();
        }
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

    blueos_driver::systimer::esp32_sys_timer::Esp32SysTimer::<0x6000_A000, 16_000_000>::init();

    unsafe {
        write32(PLIC_MX_THRESH, 1);
        route_source(INTMTX_USB_SERIAL_JTAG_MAP, USB_SERIAL_JTAG_INT_NUM, 15);
        route_source(INTMTX_SYSTIMER_TARGET0_MAP, TARGET0_INT_NUM, 15);
    }

    unsafe {
        core::arch::asm!(
            "csrc mideleg, {mask}",
            mask = in(reg) MIDELEG_DELEG_MASK,
            options(nostack, preserves_flags),
        );
    }

    crate::time::Tick::interrupt_after(crate::time::Tick(1));

    // ------------------------------------------------------------------
    // 系统时钟树 configure():MSPI HS 分频 + SOC_ROOT_CLK 选择。
    //
    // 移植自 esp-hal-1.1.1 src/soc/esp32c6/clocks.rs::ClockConfig::configure()
    // (clocks.rs:102-117)。esp-hal 在切到 PLL 前强制先把 MSPI 源时钟 HS 分频设成
    // /6(=80MHz),因为 C6 的 MSPI HS 分频复位默认给 120MHz,校准前不可用——若
    // 不预先设好,切 PLL 后 flash 取指/数据访问会在高负载时出错。
    //   PLL = 480MHz,div_num=5 → 480/(5+1)=80MHz(esp-hal MspiFastHsClkDivisor::_5)。
    // SOC_ROOT_CLK 选 PLL(soc_clk_sel[1:0]=1),与 esp-hal soc_root_clk=Pll 一致。
    //
    // 偏移取自本地 PAC esp32c6-0.23.0(pcr.rs 各寄存器访问器的 #[doc] 地址注释,
    // 这是 svd2rust 生成的权威块内偏移,不能用 RegisterBlock 字段序号数——字段
    // 声明顺序 ≠ 硬件地址顺序):
    //   PCR base = 0x6009_6000 (lib.rs:692)
    //   PCR_SYSCLK_CONF    @ +0x110 → 0x6009_6110 (pcr.rs:383 "0x110 - SYSCLK ...")
    //     soc_clk_sel = Bits[1:0] (0=XTAL, 1=SPLL, 2=FOSC)。TRM 7.2.4.3:WiFi/BLE
    //     只能在 soc_clk_sel=1(PLL) 时工作,故必须显式切到 PLL。
    //   PCR_MSPI_CLK_CONF  @ +0x1c  → 0x6009_601C (pcr.rs:97 "0x1c - MSPI_CLK ...")
    //     mspi_fast_hs_div_num = Bits[7:0] (值 5 = div6 → 480MHz/6 = 80MHz,
    //     esp-hal MspiFastHsClkDivisor::_5)。
    // 注:系统能从 flash 启动,说明 bootloader 已把 PLL 起振 + MSPI 设在 80MHz,本段
    // 主要是对齐 esp-hal 标准初始化、防边界情况,属"应做但未做"的收尾。
    unsafe {
        const PCR_BASE: usize = 0x6009_6000;
        const PCR_SYSCLK_CONF: usize = PCR_BASE + 0x110;
        const PCR_MSPI_CLK_CONF: usize = PCR_BASE + 0x1c;

        // soc_clk_sel = Bits[16:17] (PCR_SOC_CLK_SEL_S=16, IDF pcr_reg.h:1621 +
        // PAC sysclk_conf.rs). 0=XTAL, 1=SPLL(PLL). WiFi/BLE 只能在 PLL 下工作,
        // 故必须切到 1。注意字段在 bit16-17,不是 bit0-1(bit0-7 是 LS_DIV_NUM)。
        // 保留其他位。
        let v = read32(PCR_SYSCLK_CONF);
        write32(PCR_SYSCLK_CONF, (v & !(0x3 << 16)) | (0x1 << 16));

        // mspi_fast_hs_div_num = Bits[8:15] (PCR_MSPI_FAST_HS_DIV_NUM_S=8). 值 5
        // = div6 → 480MHz/6 = 80MHz。注意字段在 bit8-15,不是 bit0-7。保留其他位。
        let v = read32(PCR_MSPI_CLK_CONF);
        write32(PCR_MSPI_CLK_CONF, (v & !(0xFF << 8)) | (5 << 8));
    }

    unsafe {
        disable_wdt(LP_WDT_WPROTECT, LP_WDT_CONFIG0, 1 << 12);
        disable_wdt(TIMG0_WDT_WPROTECT, TIMG0_WDT_CONFIG0, 0);
    }

    // ------------------------------------------------------------------
    // WiFi modem 时钟使能:这是 C3 板级(seeed_xiao_esp32c3/mod.rs:149-172
    // power_domain.enable_wifi() + 写 SYSTEM_WIFI_CLK_EN_REG)的 C6 对应,C6 此前漏做,
    // 导致 driver 控制链路通(scan 启动/ScanDone 正常)但 RF RX 收不到任何 802.11 帧
    // ——recv_cb_sta 零调用、scan number=0。
    //
    // 移植自 esp-radio 0.18 src/radio_clocks/clocks_ll/esp32c6.rs::enable_wifi(true),
    // 寄存器基址/字段偏移取自本地 PAC esp32c6-0.23.0(同 esp-hal 1.1.1 所用):
    //   MODEM_SYSCON @ 0x600A_9800,RegisterBlock 首字段 test_conf @0x00,
    //     故 clk_conf1 @ +0x14 → 0x600A_9814(modem_rst_conf @ +0x10 → 0x600A_9810
    //     与下方 wifi_reset_mac 注释一致,坐实偏移)。
    //   MODEM_LPCON  @ 0x600A_F000,clk_conf 是第 7 字段 @ +0x18 → 0x600A_F018。
    // 用 RMW(read-modify-write)保留其他位,只置 wifi/fe 域时钟使能位。
    unsafe {
        const MODEM_SYSCON_CLK_CONF1: usize = 0x600A_9814;
        // clk_conf1 的 wifi/fe 时钟使能位(共 16 位,PAC esp32c6/clk_conf1.rs reader 位号):
        //   bit0-10: wifibb_22m/40m/44m/80m/40x/80x/40x1/80x1/160x1 + wifimac + wifi_apb
        //   bit13-16: fe_80m / fe_160m / fe_cal_160m / fe_apb
        // bit11(fe_20m)、bit12(fe_40m)不在 enable_wifi 置位范围,保持原值。
        const CLK_CONF1_WIFI_FE_MASK: u32 = 0x0001_F7FF; // bit0-10 | bit13-16
        let v = read32(MODEM_SYSCON_CLK_CONF1);
        write32(MODEM_SYSCON_CLK_CONF1, v | CLK_CONF1_WIFI_FE_MASK);

        const MODEM_LPCON_CLK_CONF: usize = 0x600A_F018;
        // bit0 clk_wifipwr_en | bit1 clk_coex_en(PAC esp32c6/modem_lpcon/clk_conf.rs)
        const LPCON_WIFIPWR_COEX_MASK: u32 = 0x3;
        let v = read32(MODEM_LPCON_CLK_CONF);
        write32(MODEM_LPCON_CLK_CONF, v | LPCON_WIFIPWR_COEX_MASK);

        // ------------------------------------------------------------------
        // PMU ICG 门控 + power_st 状态映射 + wifi_lp_clk_conf:
        // 移植自 esp-radio 0.18 src/radio_clocks/clocks_ll/esp32c6.rs::init_clocks()。
        //
        // 仅 enable_wifi(上一块)不够的原因:C6 把 modem 时钟拆到 MODEM_SYSCON/
        // MODEM_LPCON/PMU 三域,PMU 用 ICG(input clock gating)门控 modem 时钟。
        // esp-phy 的 C6 enable_phy(phy_clocks_ll_esp32c6.rs)只开 PHY 校准用的 I2C
        // master 时钟,故意不开 WiFi modem 时钟——正常使用时由 esp_radio::init() →
        // init_radio_clocks() → init_clocks() 配好 PMU ICG + power_st + lp_clk。
        // 但 BlueOS 绕过了 esp_radio::init()(esp32_wlan/mod.rs:1008 直接调
        // esp_wifi_init_internal 进 driver,driver 反过来调 BlueOS 的 wifi_clock_enable
        // 空 no-op),导致 PMU ICG 门控从未配置,modem 时钟被锁死,RF RX 收不到任何
        // 802.11 帧——scan number=0、recv_cb_sta 零调用。C3 无此 PMU ICG 层(其
        // enable_phy 直接开 APB_CTRL.wifi_clk_en 全套),故 C3 能 scan 而 C6 不能。
        //
        // 寄存器偏移取自 PAC esp32c6-0.23.0 各 RegisterBlock 访问器上的
        // #[doc = "0xNN"] 注释;位号取自各字段定义 .rs 的 #[doc = "Bits X:Y"]。
        // ------------------------------------------------------------------

        // ① PMU ICG 门控(PMU 基址 0x600B_0000)。
        // 三个 *_icg_modem_code 都是 bits[31:30] 的 2 位字段(PAC FieldWriter 起始位 30),
        // 分别配置 sleep/modem/active 三个电源状态下 modem 时钟的 ICG code:
        //   sleep  = 0(关 modem 时钟门控,允许进入低功耗时也保留),
        //   modem  = 1(modem 状态下中等门控),
        //   active = 2(active 状态下最少门控,时钟常通)。
        // 用 RMW 清 bits[31:30] 再写入目标值,保留低 30 位。
        const PMU_BASE: usize = 0x600B_0000;
        const PMU_HP_SLEEP_ICG_MODEM: usize = PMU_BASE + 0x74;
        const PMU_HP_MODEM_ICG_MODEM: usize = PMU_BASE + 0x40;
        const PMU_HP_ACTIVE_ICG_MODEM: usize = PMU_BASE + 0x0C;
        const ICG_MODEM_CODE_FIELD: u32 = 0b11 << 30; // bits[31:30]
        // sleep code = 0:清零该字段即可
        let v = read32(PMU_HP_SLEEP_ICG_MODEM);
        write32(PMU_HP_SLEEP_ICG_MODEM, v & !ICG_MODEM_CODE_FIELD);
        // modem code = 1
        let v = read32(PMU_HP_MODEM_ICG_MODEM);
        write32(PMU_HP_MODEM_ICG_MODEM, (v & !ICG_MODEM_CODE_FIELD) | (1 << 30));
        // active code = 2
        let v = read32(PMU_HP_ACTIVE_ICG_MODEM);
        write32(PMU_HP_ACTIVE_ICG_MODEM, (v & !ICG_MODEM_CODE_FIELD) | (2 << 30));

        // imm_modem_icg @ 0xDC:bit31 update_dig_icg_modem_en——置 1 触发上述 ICG code
        // 立即生效(PAC BitWriter 起始位 31)。write-only 触发位,直接写 1<<31。
        const PMU_IMM_MODEM_ICG: usize = PMU_BASE + 0xDC;
        write32(PMU_IMM_MODEM_ICG, 1 << 31);

        // imm_sleep_sysclk @ 0xD0:bit28 update_dig_icg_switch——置 1 触发时钟开关切换
        // 立即生效(PAC BitWriter 起始位 28;同寄存器 bit29/30/31 是别的字段,只置 bit28)。
        const PMU_IMM_SLEEP_SYSCLK: usize = PMU_BASE + 0xD0;
        write32(PMU_IMM_SLEEP_SYSCLK, 1 << 28);

        // ② power_st 状态映射:把 modem 各子域时钟映射到电源状态机的 state map。
        // 每个 *_st_map 是 4 位字段,值 6 表示"该时钟在对应电源状态下使能"。
        // MODEM_SYSCON.clk_conf_power_st @ 0x600A_980C(PAC 偏移 0x0C):
        //   clk_modem_apb_st_map  [31:28] = 6
        //   clk_modem_peri_st_map [27:24] = 4
        //   clk_wifi_st_map       [23:20] = 6
        //   clk_bt_st_map         [19:16] = 6
        //   clk_fe_st_map         [15:12] = 6
        //   clk_zb_st_map         [11:8]  = 6
        const MODEM_SYSCON_CLK_CONF_POWER_ST: usize = 0x600A_980C;
        // 低 8 位 [7:0] 无字段,保留原值;高 24 位按上面赋值。
        // 直接拼:apb=6<<28 | peri=4<<24 | wifi=6<<20 | bt=6<<16 | fe=6<<12 | zb=6<<8
        const SYSCON_POWER_ST_HI: u32 = (6 << 28) | (4 << 24) | (6 << 20)
            | (6 << 16) | (6 << 12) | (6 << 8);
        let lo = read32(MODEM_SYSCON_CLK_CONF_POWER_ST) & 0xFF;
        write32(MODEM_SYSCON_CLK_CONF_POWER_ST, SYSCON_POWER_ST_HI | lo);

        // MODEM_LPCON.clk_conf_power_st @ 0x600A_F020(PAC 偏移 0x20):
        //   clk_lp_apb_st_map   [31:28] = 6
        //   clk_i2c_mst_st_map  [27:24] = 6
        //   clk_coex_st_map     [23:20] = 6
        //   clk_wifipwr_st_map  [19:16] = 6
        // 低 16 位 [15:0] 无字段,保留原值。
        const MODEM_LPCON_CLK_CONF_POWER_ST: usize = 0x600A_F020;
        const LPCON_POWER_ST_HI: u32 = (6 << 28) | (6 << 24) | (6 << 20) | (6 << 16);
        let lo = read32(MODEM_LPCON_CLK_CONF_POWER_ST) & 0xFFFF;
        write32(MODEM_LPCON_CLK_CONF_POWER_ST, LPCON_POWER_ST_HI | lo);

        // ③ WiFi 低功耗时钟源:MODEM_LPCON.wifi_lp_clk_conf @ 0x600A_F00C(PAC 偏移 0x0C)。
        // 置 4 个时钟源选择位(bit0 osc_slow | bit1 osc_fast | bit2 xtal | bit3 xtal32k)
        // 全选(esp-radio 原样四个 set_bit)+ clk_wifipwr_lp_div_num[15:4] = 0。
        // 全选多源 + div=0 是 esp-idf/esp-radio 对 C6 wifipwr 低功耗时钟的默认配置。
        const MODEM_LPCON_WIFI_LP_CLK_CONF: usize = 0x600A_F00C;
        const LPCON_LP_CLK_SEL_MASK: u32 = 0b1111; // bit0-3 四个 sel 位
        const LPCON_LP_DIV_NUM_MASK: u32 = 0xFFF0; // bits[15:4] div_num
        let v = read32(MODEM_LPCON_WIFI_LP_CLK_CONF);
        // 清 div_num 再置 4 个 sel 位,其余位保留
        write32(
            MODEM_LPCON_WIFI_LP_CLK_CONF,
            (v & !LPCON_LP_DIV_NUM_MASK) | LPCON_LP_CLK_SEL_MASK,
        );

        // ------------------------------------------------------------------
        // ④ [第三阶段修复] PMU HP system init:active/modem/sleep 三态 ck_power
        // 置 BBPLL 上电位(XPD_BBPLL | XPD_BBPLL_I2C | XPD_BB_I2C)。
        //
        // 根因(运行时 dump 坐实,2026-08-06):第二阶段补完 init_clocks() 后 scan 仍
        // 0 AP,trace 坐实中断链路全通(分支 C),根因回 RF/PHY 物理层。在
        // esp_wifi_init_internal 前后各 dump PMU 关键寄存器(esp32_wlan/mod.rs 的
        // dump_pmu_rf_regs),实测 before==after 且:
        //   PMU_HP_ACTIVE_HP_CK_POWER @ 0x600B_0014 = 0x0
        //     → XPD_BBPLL(bit30)=0, XPD_BBPLL_I2C(bit29)=0, XPD_BB_I2C(bit28)=0
        //   全为复位 default 0,driver/libnet80211 的 init_internal 完全没碰这些 PMU
        //   寄存器(确认 driver 不补 pmu_init)。
        // BBPLL 是 RF 本振源(480MHz,经分频给 RF mixer 做下变频),没上电 = RF
        // 无本振 = RX 无法解调任何 802.11 帧 → scan 0 AP、recv_cb_sta 零调用。
        // CPU 能跑、scan 能起能完成,是因为 active 态系统时钟选 XTAL(40MHz 直供,
        // 不依赖 BBPLL),但 RF 的本振必须靠 BBPLL——这与"控制链路全通、RF RX 零帧"
        // 的现象完全吻合。C3 无 PMU,用 RTC_CNTL + esp-phy 直接开 BBPLL,故 C3 能 scan。
        //
        // 漏因:IDF `pmu_init()`(esp_idf/components/esp_hw_support/port/esp32c6/
        // pmu_init.c:209,由 esp_clk_init 调用,是 app 运行时初始化非 bootloader)
        // 调 `pmu_hp_system_init_default`,对 active/modem/sleep 三态都把这三个 XPD
        // 位置 1(等价 esp-hal HpSystemInit::active/modem/sleep 的
        // power.clk.set_xpd_bb_i2c(true)/set_xpd_bbpll_i2c(true)/set_xpd_bbpll(true),
        // 见 esp-hal-1.1.1 src/rtc_cntl/rtc/esp32c6.rs:542-544 与 625-630)。BlueOS
        // 绕过整个 IDF/esp-hal 系统初始化(grep esp_hal::init / HpSystemInit 零命中),
        // 这三态 ck_power 从未被配置,保留复位值 0。
        //
        // 修复:对 active/modem/sleep 三态各自的 HP_CK_POWER 寄存器 RMW 置位
        //   bit28 XPD_BB_I2C      — BB(基带)i2c 控制上电
        //   bit29 XPD_BBPLL_I2C   — BBPLL i2c 控制上电
        //   bit30 XPD_BBPLL       — BBPLL 本振上电(主)
        // 三态位号相同(IDF pmu_reg.h 逐态核实:HP_ACTIVE/HP_MODEM/HP_SLEEP 的
        // XPD_BB_I2C/XPD_BBPLL_I2C/XPD_BBPLL 都是 bit28/29/30,default 全 0)。
        // 只置不清(RMW 用 OR),不动 bit26 I2C_ISO_EN / bit27 I2C_RETENTION
        // (esp-hal 置 false,实测 ck_power=0x0 即 bit26/27 本就 0,符合期望)。
        // active scan 期间 PMU 会在 active/modem 态间切,补全三态避免任一态掉 BBPLL。
        //
        // 偏移取自 IDF components/soc/esp32c6/register/soc/pmu_reg.h:
        //   PMU_HP_ACTIVE_HP_CK_POWER_REG = 0x600B_0000 + 0x14
        //   PMU_HP_MODEM_HP_CK_POWER_REG  = 0x600B_0000 + 0x48
        //   PMU_HP_SLEEP_HP_CK_POWER_REG  = 0x600B_0000 + 0x7C
        const XPD_BBPLL_MASK: u32 = (1 << 30) | (1 << 29) | (1 << 28); // bit30|bit29|bit28
        // active 态(0x14):dump 实测=0x0,置位后=0x7000_0000
        let v = read32(PMU_BASE + 0x14);
        write32(PMU_BASE + 0x14, v | XPD_BBPLL_MASK);
        // modem 态(0x48):WiFi modem 工作态,务必上电
        let v = read32(PMU_BASE + 0x48);
        write32(PMU_BASE + 0x48, v | XPD_BBPLL_MASK);
        // sleep 态(0x7C):2026-08-10 纠错——esp-hal HpSystemInit::sleep() 只置
        // xpd_bb_i2c(bit28)=true,xpd_bbpll_i2c(bit29)/xpd_bbpll(bit30) 都是 false
        // (esp32c6.rs:718-720)。sleep 态本振下电是正常的(睡眠不需要 RF),旧代码
        // 置三位全 1 会把睡眠态的 BBPLL 强行上电,与 esp-hal 语义冲突。改为只置 bit28。
        let v = read32(PMU_BASE + 0x7C);
        write32(PMU_BASE + 0x7C, v | (1 << 28)); // only XPD_BB_I2C

        // ------------------------------------------------------------------
        // ⑥ [第三阶段修复续] PMU HP analog 子系统:bias + regulator0(dbias)。
        //
        // 根因补全:④ 只置了 BBPLL 的 XPD 位(允许上电),但 BBPLL 能否起振到正确
        // 480MHz 还取决于**工作点电压 dbias**。esp-hal HpSystemInit 三态都对
        // regulator0.dbias 设了校准值(active/modem=HP_CALI_DBIAS=25, sleep=1),
        // 且 init() 末尾([esp32c6.rs:1092-1094])又显式重写 hp_active_hp_regulator0
        // 的 dbias=25——坐实这是 BBPLL 起振的必要条件。BlueOS 绕过整段,dbias 保持
        // 复位 0 → 工作点电压不对 → BBPLL 起振不到 480MHz → RX 仍无法解调。
        //
        // 三态语义(逐行核实 esp-hal active/modem/sleep,bitfield 位号核实自
        // esp32c6.rs:315-345 的 HpAnalogBias/HpAnalogRegulator0 bitfield):
        //   HpAnalogBias        位:xpd_bias=25, dbg_atten=[29:26], pd_cur=30, bias_sleep=31
        //   HpAnalogRegulator0  位:xpd=18, dbias=[31:27], slp_mem_xpd=16, slp_logic_xpd=17
        //
        // 偏移核实自 esp32c6 PAC(esp32c6-0.23.0/src/pmu.rs RegisterBlock accessor doc):
        //   hp_active_bias           @ 0x18   hp_active_hp_regulator0  @ 0x28
        //   hp_modem_bias            @ 0x4c   hp_modem_hp_regulator0   @ 0x5c
        //   hp_sleep_bias            @ 0x80   hp_sleep_hp_regulator0   @ 0x90
        // (hp_sleep 的 analog 本次不补——sleep 态 dbias=1、bias 全 false,与 ④sleep
        //  一致属"睡眠不需要 RF",且 scan 在 active/modem 态进行,sleep 不影响扫描。)
        //
        // RMW 原则:只置/清目标位,不动 slp_mem_*/slp_logic_* 等 default 字段。
        const HP_CALI_DBIAS: u32 = 25; // esp-hal HP_CALI_DBIAS(esp32c6.rs:219),active/modem 工作点
        const DBIAS_SHIFT: u32 = 27;   // regulator0.dbias 字段起始位 [31:27]
        const REG0_XPD_BIT: u32 = 1 << 18; // regulator0.xpd(bit18)=HP regulator 上电
        const BIAS_XPD_BIT: u32 = 1 << 25; // bias.xpd_bias(bit25)=bias 上电

        // active 态:bias.xpd_bias=true, regulator0.xpd=true + dbias=25
        // (esp-hal active():570-586)。bias 置 bit25;regulator0 置 bit18 | (25<<27)。
        let v = read32(PMU_BASE + 0x18);
        write32(PMU_BASE + 0x18, v | BIAS_XPD_BIT);
        let v = read32(PMU_BASE + 0x28);
        write32(PMU_BASE + 0x28, v | REG0_XPD_BIT | (HP_CALI_DBIAS << DBIAS_SHIFT));

        // modem 态(★scan 实际工作态):bias.xpd_bias=**false**(反直觉但 esp-hal
        // modem():663 就这么设——modem 态靠 regulator 供电,不开 bias),regulator0
        // .xpd=true + dbias=25(modem():670-673)。bias 清 bit25;regulator0 置 bit18
        // | (25<<27)。
        let v = read32(PMU_BASE + 0x4c);
        write32(PMU_BASE + 0x4c, v & !BIAS_XPD_BIT); // clear: modem 态 bias 关
        let v = read32(PMU_BASE + 0x5c);
        write32(PMU_BASE + 0x5c, v | REG0_XPD_BIT | (HP_CALI_DBIAS << DBIAS_SHIFT));

        // ------------------------------------------------------------------
        // ⑤ [第三阶段修复续 + 2026-08-10 纠错] PMU RF i2c 控制总线上电。
        //
        // 纠错(凭印象翻车第五轮,已从 esp32c6 PAC esp32c6-0.23.0/src/pmu.rs 逐个
        // accessor 的 doc 偏移 + rf_pwc.rs 位定义核实):
        //   旧代码把 RF_PWC 当三态写 0x150/0x154/0x158 且 mask=0xFC00_0000(置
        //   bit26..31 六位)。真相:
        //   (a) RF_PWC 是**单一寄存器** @ 0x154(PAC RegisterBlock 中 rf_pwc 字段
        //       偏移 0x154,非三态)。0x150=POR_STATUS_REG(只读,写无效),旧代码
        //       读到的 0x80000000 是 POR 完成标志;0x158=BACKUP_CFG_REG(可写,旧
        //       代码把它写坏成 0xFC00_0000,待后续评估恢复)。
        //   (b) esp-hal rtc::init()(= IDF pmu_init(),[esp32c6.rs:1019-1021]
        //       (external/vendor/esp-hal-1.1.1/src/rtc_cntl/rtc/esp32c6.rs#L1019))
        //       对 RF_PWC 只 RMW 置两位:
        //         perif_i2c_rstb (bit26) = 1   perif i2c 解复位
        //         xpd_perif_i2c (bit27) = 1   perif i2c 电源开
        //       bit28..31(xpd_txrf_i2c/xpd_rfrx_pbus/xpd_ckgen_i2c/xpd_pll_i2c)
        //       **不动**——RF 前端这些子域的 XPD 由 PHY 层(esp_phy_init / regi2c
        //       / BBPLL 起振后)管理,pmu_init 不越权。旧代码置六位是过度上电。
        //   (c) RF_PWC RESET_VALUE = 0x0800_0000(rf_pwc.rs:119),即复位 default
        //       bit27(xpd_perif_i2c)=1 已开,bit26(perif_i2c_rstb)=0 待置 1。
        //       RMW OR 置 bit26|27 = 0x0C00_0000,与 esp-hal 完全一致。
        //
        // 修法:只对单一 RF_PWC @ 0x154 RMW 置 bit26|27。删掉 0x150/0x158 两处错写。
        const RF_PWC_I2C_MASK: u32 = (1 << 27) | (1 << 26); // bit27 XPD_PERIF_I2C | bit26 PERIF_I2C_RSTB
        // PMU_RF_PWC @ 0x154(单一寄存器):perif i2c 控制总线上电 + 解复位
        let v = read32(PMU_BASE + 0x154);
        write32(PMU_BASE + 0x154, v | RF_PWC_I2C_MASK);

        // ===== BBPLL 自校准 + regi2c ENIF(补 IDF 链路缺口 1 & 2)=====
        // 顺序:① ENIF 四位先(dig/rtc 稳压器进入自校准模式)② BBPLL 自校准
        // (本振频偏校正,RF 解调前置条件)。两者都走 ana i2c master,perif_i2c
        // 刚在 RF_PWC 上电解复位,总线可用。
        regi2c_enif_init();
        bbpll_calibrate();
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
