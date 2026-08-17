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
use crate::kearly_println;
use blueos_driver::uart::esp32_usb_serial::Esp32UsbSerialIsr;
use blueos_hal::{isr::IsrDesc, Has8bitDataReg};

pub type ClockImpl =
    blueos_driver::systimer::esp32_sys_timer::Esp32SysTimer<0x6000_a000, 16_000_000>;

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
const PLIC_MX_ENABLE: usize = PLIC_MX_BASE;
const PLIC_MX_TYPE: usize = PLIC_MX_BASE + 0x4;
#[allow(dead_code)] // kept for [BISECT-ROUND3] restore
const PLIC_MX_CLEAR: usize = PLIC_MX_BASE + 0x8;
const PLIC_MX_EIP_STATUS: usize = PLIC_MX_BASE + 0xC;
const PLIC_MX_PRI: usize = PLIC_MX_BASE + 0x10; // PRI[line] @ PLIC_MX_PRI + line*4
const PLIC_MX_THRESH: usize = PLIC_MX_BASE + 0x90;

const MIDELEG_UEXT_BIT: usize = 1 << 8;
const MIDELEG_UTIMER_BIT: usize = 1 << 4;
const MIDELEG_USOFT_BIT: usize = 1 << 0;
/// One-shot clear of the three delegation bits (bit0|bit4|bit8) in mideleg's
/// reset value 0x111.
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

// Access Path Manager (APM) filter registers. C6 has three APM instances
// (LP_APM / LP_APM0 / HP_APM). Their func_ctrl defaults to TEE-only mode, so
// every master except the HP CPU boots in REE mode and gets DENIED on memory
// access — including WiFi DMA descriptor fetches. esp-hal disables all three in
// pre_init (esp-hal-1.1.1 src/soc/esp32c6/mod.rs:31-49). Base addresses from
// PAC esp32c6-0.23.0 (lib.rs:413/521/530); func_ctrl sits at +0xC4 in each
// RegisterBlock (region_filter_en@0x0 + region cluster -> 0xC4, confirmed in
// hp_apm.rs / lp_apm.rs / lp_apm0.rs).
const LP_APM_FUNC_CTRL: usize = 0x600B_3800 + 0xC4;
const LP_APM0_FUNC_CTRL: usize = 0x6009_9800 + 0xC4;
const HP_APM_FUNC_CTRL: usize = 0x6009_9000 + 0xC4;

// Machine External Interrupt Enable bit in the mie CSR (standard RISC-V bit 11).
// esp-hal writes `csrw mie, u32::MAX` (esp-hal-1.1.1 src/interrupt/riscv.rs:554),
// enabling MEIE alongside any per-line bits. blueos only sets the per-line bit
// (1 << line); if C6's mie also gates the aggregated external interrupt through
// MEIP, per-line alone is not enough. Set this alongside the per-line bit.
#[allow(dead_code)] // kept for [BISECT-ROUND2] restore
const MIE_MEIE_BIT: usize = 1 << 11;

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
        // Enable the per-line bit plus the aggregated MEIE (bit 11) so the
        // external interrupt can reach the CPU whichever gating model C6 uses.
        // [BISECT-ROUND2] MEIE (bit11) temporarily dropped to test whether it
        // is the WiFi-interrupt root cause. Restore `| MIE_MEIE_BIT` after.
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
// Ana I2C master protocol + BBPLL self-calibration + regi2c ENIF
//
// Background: BlueOS bypasses IDF system init (esp_rtc_init / pmu_init), so two
// things were never done:
//   Gap 1 — BBPLL regi2c self-calibration (rtc_clk.c:155 rtc_clk_bbpll_configure, 5 steps)
//   Gap 2 — regi2c ENIF four bits (4x REGI2C_WRITE_MASK at pmu_init.c:214-217)
// Both require ana I2C master register access to analog slaves (BBPLL=0x66 /
// DIG_REG=0x6D). The C6 ROM does not export esp_rom_regi2c_write(_mask) symbols
// (absent from esp32c6.rom.api.ld; phy.ld only has rom_i2c_enter/exit_critical),
// so FFI is not viable — the I2C protocol must be written raw here.
//
// Protocol ported from esp-idf patches/esp_rom_regi2c_esp32h2.c (shared by
// C6/H2). Register addresses / field bit numbers verified one-by-one against
// components/soc/esp32c6/register/soc/i2c_ana_mst_reg.h and
// components/soc/esp32c6/include/soc/regi2c_defs.h:
//   DR_REG_I2C_ANA_MST_BASE = 0x600AF800 (reg_base.h:58)
//   I2C_ANA_MST_I2C0_CTRL_REG    @ +0x00 → 0x600AF800
//     bit[7:0]   SLAVE_ID    (block id, e.g. 0x66=BBPLL / 0x6D=DIG_REG)
//     bit[15:8]  ADDR        (8-bit reg offset inside the slave)
//     bit[23:16] DATA        (value written on writes, value read on reads)
//     bit24      WR_CNTL     (0=read, 1=write)
//     bit25      BUSY        (RO, 1=transfer in progress, poll until 0)
//   I2C_MST_ANA_CONF0_REG  @ +0x18 → 0x600AF818
//     bit2  BBPLL_STOP_FORCE_HIGH  (set 1 to stop calibration, pull stop high)
//     bit3  BBPLL_STOP_FORCE_LOW   (set 1 to start calibration, pull stop low)
//     bit24 BBPLL_CAL_DONE         (RO, 1=calibration done)
//   I2C_MST_ANA_CONF1_REG  @ +0x1C → 0x600AF81C (R/W, 24-bit slave RD mask)
//   I2C_MST_ANA_CONF2_REG  @ +0x20 → 0x600AF820 (R/W, 24-bit slave MST_SEL)
//     bit9  BBPLL_MST_SEL
//     bit12 DIG_REG_MST_SEL
//   i2c_sel semantics (see esp_rom_hp_regi2c_esp32c6.c:115 `return i2c_sel ? 0 : 1`):
//   MST_SEL bit set   → use I2C0 (+0x00); MST_SEL bit clear → use I2C1 (+0x04).
//   CONF2 reset = 0x0004 (bit2 only), BBPLL_MST_SEL(bit9)/DIG_REG_MST_SEL(bit12)
//   both reset to 0 → default routes through I2C1. This is counter-intuitive but
//   confirmed hardware routing: MST_SEL=1 selects I2C0, MST_SEL=0 selects I2C1.
//   Earlier this was inverted (assumed 1=I2C1), causing ENIF readback all 0xff.
//   CONF1 RD_MASK: writing CONF1 = (~target RD bit) & 0xFFFFFF disconnects the
//   read paths of the other analog slaves, leaving only the target slave live.
//   MODEM_LPCON.clk_conf.clk_i2c_mst_en (bit2) gates the ana I2C master clock
//   (regi2c_ctrl_ll_master_enable_clock; esp-phy enable_phy also enables it, but
//   calibration runs before PHY enable, so set it again here to be safe).
// ===================================================================

// Ana I2C master register block base (DR_REG_I2C_ANA_MST_BASE)
const I2C_ANA_MST_BASE: usize = 0x600A_F800;
const I2C_ANA_MST_I2C0_CTRL: usize = I2C_ANA_MST_BASE; // +0x00
const I2C_ANA_MST_I2C1_CTRL: usize = I2C_ANA_MST_BASE + 0x04;
const I2C_MST_ANA_CONF0: usize = I2C_ANA_MST_BASE + 0x18; // BBPLL calibration control
const I2C_MST_ANA_CONF1: usize = I2C_ANA_MST_BASE + 0x1C; // slave RD mask
const I2C_MST_ANA_CONF2: usize = I2C_ANA_MST_BASE + 0x20; // slave MST_SEL

// MODEM_LPCON.clk_conf @ 0x600A_F018, bit2 = clk_i2c_mst_en (ana I2C master clock)
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
const REGI2C_DIG_REG: u8 = 0x6D;

// Slave select masks for I2C_MST_ANA_CONF1 (RD_MASK: clear target bit, keep others)
// CONF1 bit6=BIAS / bit7=BBPLL / bit8=ULP / bit9=SAR / bit10=DIG_REG
const REGI2C_BBPLL_RD_MASK: u32 = !(1 << 7) & 0x00FF_FFFF;
const REGI2C_DIG_REG_RD_MASK: u32 = !(1 << 10) & 0x00FF_FFFF;
// Slave select bits for I2C_MST_ANA_CONF2 (MST_SEL: 1=route to I2C1)
const REGI2C_BBPLL_MST_SEL: u32 = 1 << 9;
const REGI2C_DIG_REG_MST_SEL: u32 = 1 << 12;

// ROM ets_delay_us absolute address = 0x40000040 (strong symbol, esp32c6.rom.ld:31).
// link.x does not INCLUDE esp32c6.rom.ld, so the symbol cannot be extern-imported
// (would be undefined reference); instead call via a raw-address function pointer,
// bypassing linker symbol resolution. Signature: void ets_delay_us(uint32_t us),
// RISC-V calling convention: a0 = us.
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
const I2C_BBPLL_OC_REF_DIV: u8 = 0x02;
const I2C_BBPLL_OC_DIV_7_0: u8 = 0x03;
const I2C_BBPLL_OC_DR1: u8 = 0x05;
const I2C_BBPLL_OC_DR3: u8 = 0x05;
const I2C_BBPLL_OC_DCUR: u8 = 0x06;
const I2C_BBPLL_OC_VCO_DBIAS: u8 = 0x09;
const BBPLL_OC_DCUR_40M: u8 = (1 << 6) | (3 << 4) | 3;
const BBPLL_OC_REF_DIV_40M: u8 = 5 << 4;
const BBPLL_OC_DIV_7_0_40M: u8 = 8;

/// BBPLL regi2c self-calibration — reproduces rtc_clk_bbpll_configure() in
/// esp-idf components/esp_hw_support/port/esp32c6/rtc_clk.c:155-171.
///
/// Five steps: ① enable ana I2C master clock ② start calibration (clear bit2 /
/// set bit3) ③ write the BBPLL slave OC_* frequency config (480MHz @ 40MHz XTAL)
/// ④ poll CAL_DONE (bit24) ⑤ stop calibration (clear bit3 / set bit2) + 10us wait
/// + disable I2C clock. The BBPLL is the RF local oscillator source; the bootloader
/// starts it oscillating but never self-calibrates, so the frequency offset makes
/// RX unable to demodulate 802.11 frames → scan 0 AP.
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
        // WiFi interrupt: libnet80211 aggregates the WIFI_MAC/WIFI_PWR sources
        // into CPU intr 1 (see esp32_wlan::api::set_isr ISR_INTERRUPT_1); once the
        // trap fires it is dispatched here. Structurally identical to the C3 board
        // seeed_xiao_esp32c3/mod.rs:97-100.
        0 | 1 => {
            #[cfg(enable_net)]
            {
                crate::net::link::esp32_wlan::api::ISR_INTERRUPT_1.dispatch();
            }
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

    blueos_driver::systimer::esp32_sys_timer::Esp32SysTimer::<0x6000_a000, 16_000_000>::init();

    unsafe {
        // Disable the three Access Path Manager (APM) filters early. Their func_ctrl
        // defaults to TEE-only, denying all REE-mode masters — including WiFi DMA.
        // Ported from esp-hal-1.1.1 src/soc/esp32c6/mod.rs:31-49 pre_init.
        // [ROOT CAUSE] Confirmed via 4-round bisect (2026-08-14): of the four
        // esp-hal-vs-blueos WiFi-interrupt gaps, disabling APM is the sole change
        // that makes WiFi interrupts fire. REE-mode WiFi DMA is denied bus access
        // by the TEE-only func_ctrl default until APM is disabled; without it the
        // MAC can never complete a DMA fetch, so the "rx done" interrupt is never
        // raised regardless of INTMTX/PLIC_MX/mie configuration.
        write32(LP_APM_FUNC_CTRL, 0);
        write32(LP_APM0_FUNC_CTRL, 0);
        write32(HP_APM_FUNC_CTRL, 0);

        // PLIC_MX threshold: only interrupts with prio > thresh fire.
        // [BISECT-ROUND1] temporarily restored to 1 (original value) to test
        // whether threshold=0 was the WiFi-interrupt root cause. If scan still
        // finds APs with thresh=1, this change was NOT the root cause.
        write32(PLIC_MX_THRESH, 1);
        route_source(INTMTX_USB_SERIAL_JTAG_MAP, USB_SERIAL_JTAG_INT_NUM, 15);
        route_source(INTMTX_SYSTIMER_TARGET0_MAP, TARGET0_INT_NUM, 15);
    }

    // unsafe {
    //     core::arch::asm!(
    //         "csrc mideleg, {mask}",
    //         mask = in(reg) MIDELEG_DELEG_MASK,
    //         options(nostack, preserves_flags),
    //     );
    // }

    //crate::time::Tick::interrupt_after(crate::time::Tick(1));

    // ------------------------------------------------------------------
    // System clock tree configure(): MSPI HS divider + SOC_ROOT_CLK selection.
    //
    // Ported from esp-hal-1.1.1 src/soc/esp32c6/clocks.rs::ClockConfig::configure()
    // (clocks.rs:102-117). esp-hal forces the MSPI source-clock HS divider to /6
    // (=80MHz) before switching to PLL, because C6's MSPI HS divider reset default
    // is 120MHz and is unusable before calibration — if not preset, flash
    // instruction/data access errors out under high load after the PLL switch.
    //   PLL = 480MHz, div_num=5 → 480/(5+1)=80MHz (esp-hal MspiFastHsClkDivisor::_5).
    // SOC_ROOT_CLK selects PLL (soc_clk_sel[1:0]=1), matching esp-hal soc_root_clk=Pll.
    //
    // Offsets from the local PAC esp32c6-0.23.0 (the #[doc] address comments on each
    // register accessor in pcr.rs — these are the svd2rust-generated authoritative
    // in-block offsets; do NOT count RegisterBlock field ordinals, since field
    // declaration order != hardware address order):
    //   PCR base = 0x6009_6000 (lib.rs:692)
    //   PCR_SYSCLK_CONF    @ +0x110 → 0x6009_6110 (pcr.rs:383 "0x110 - SYSCLK ...")
    //     soc_clk_sel = Bits[1:0] (0=XTAL, 1=SPLL, 2=FOSC). TRM 7.2.4.3: WiFi/BLE
    //     only works when soc_clk_sel=1 (PLL), so must explicitly switch to PLL.
    //   PCR_MSPI_CLK_CONF  @ +0x1c  → 0x6009_601C (pcr.rs:97 "0x1c - MSPI_CLK ...")
    //     mspi_fast_hs_div_num = Bits[7:0] (value 5 = div6 → 480MHz/6 = 80MHz,
    //     esp-hal MspiFastHsClkDivisor::_5).
    unsafe {
        const PCR_BASE: usize = 0x6009_6000;
        const PCR_SYSCLK_CONF: usize = PCR_BASE + 0x110;
        const PCR_MSPI_CLK_CONF: usize = PCR_BASE + 0x1c;

        // soc_clk_sel = Bits[16:17] (PCR_SOC_CLK_SEL_S=16, IDF pcr_reg.h:1621 +
        // PAC sysclk_conf.rs). 0=XTAL, 1=SPLL(PLL). WiFi/BLE only works under PLL,
        // so must switch to 1. Note the field is at bit16-17, not bit0-1 (bit0-7 is
        // LS_DIV_NUM). Preserve other bits.
        let v = read32(PCR_SYSCLK_CONF);
        write32(PCR_SYSCLK_CONF, (v & !(0x3 << 16)) | (0x1 << 16));

        // mspi_fast_hs_div_num = Bits[8:15] (PCR_MSPI_FAST_HS_DIV_NUM_S=8). Value 5
        // = div6 → 480MHz/6 = 80MHz. Note the field is at bit8-15, not bit0-7. Preserve other bits.
        let v = read32(PCR_MSPI_CLK_CONF);
        write32(PCR_MSPI_CLK_CONF, (v & !(0xFF << 8)) | (5 << 8));
    }

    unsafe {
        disable_wdt(LP_WDT_WPROTECT, LP_WDT_CONFIG0, 1 << 12);
        disable_wdt(TIMG0_WDT_WPROTECT, TIMG0_WDT_CONFIG0, 0);
    }

    // ------------------------------------------------------------------
    // WiFi modem clock enable: this is the C6 counterpart of the C3 board
    // (seeed_xiao_esp32c3/mod.rs:149-172 power_domain.enable_wifi() + writing
    // SYSTEM_WIFI_CLK_EN_REG); C6 previously omitted it, which left the driver
    // control path working (scan start / ScanDone normal) but RF RX receiving no
    // 802.11 frames at all — recv_cb_sta never called, scan number=0.
    //
    // Ported from esp-radio 0.18 src/radio_clocks/clocks_ll/esp32c6.rs::enable_wifi(true).
    // Register base / field offsets from the local PAC esp32c6-0.23.0 (same as
    // esp-hal 1.1.1):
    //   MODEM_SYSCON @ 0x600A_9800, RegisterBlock first field test_conf @0x00,
    //     so clk_conf1 @ +0x14 → 0x600A_9814 (modem_rst_conf @ +0x10 → 0x600A_9810,
    //     consistent with the wifi_reset_mac note below, confirming the offset).
    //   MODEM_LPCON  @ 0x600A_F000, clk_conf is the 7th field @ +0x18 → 0x600A_F018.
    // Use RMW (read-modify-write) to preserve other bits, only setting the
    // wifi/fe domain clock-enable bits.
    unsafe {
        const MODEM_SYSCON_CLK_CONF1: usize = 0x600A_9814;
        // clk_conf1 wifi/fe clock-enable bits (16 bits total; PAC esp32c6/clk_conf1.rs reader bit positions):
        //   bit0-10: wifibb_22m/40m/44m/80m/40x/80x/40x1/80x1/160x1 + wifimac + wifi_apb
        //   bit13-16: fe_80m / fe_160m / fe_cal_160m / fe_apb
        // bit11 (fe_20m) and bit12 (fe_40m) are not in the enable_wifi set range, keep original value.
        const CLK_CONF1_WIFI_FE_MASK: u32 = 0x0001_F7FF; // bit0-10 | bit13-16
        let v = read32(MODEM_SYSCON_CLK_CONF1);
        write32(MODEM_SYSCON_CLK_CONF1, v | CLK_CONF1_WIFI_FE_MASK);

        const MODEM_LPCON_CLK_CONF: usize = 0x600A_F018;
        // bit0 clk_wifipwr_en | bit1 clk_coex_en (PAC esp32c6/modem_lpcon/clk_conf.rs)
        const LPCON_WIFIPWR_COEX_MASK: u32 = 0x3;
        let v = read32(MODEM_LPCON_CLK_CONF);
        write32(MODEM_LPCON_CLK_CONF, v | LPCON_WIFIPWR_COEX_MASK);

        // ------------------------------------------------------------------
        // PMU ICG gating + power_st state mapping + wifi_lp_clk_conf:
        // Ported from esp-radio 0.18 src/radio_clocks/clocks_ll/esp32c6.rs::init_clocks().
        //
        // Register offsets from the #[doc] address comments on each RegisterBlock
        // accessor in PAC esp32c6-0.23.0.

        // (1) PMU ICG gating (PMU base 0x600B_0000).
        // The three *_icg_modem_code are 2-bit fields at bits[31:30] (PAC FieldWriter
        // start bit 30), configuring the modem-clock ICG code for the sleep/modem/
        // active power states respectively:
        //   sleep  = 0 (disable modem clock gating, keep it even in low-power),
        //   modem  = 1 (medium gating in modem state),
        //   active = 2 (minimal gating in active state, clock always on).
        // Use RMW to clear bits[31:30] then write the target value, preserving the
        // low 30 bits.
        const PMU_BASE: usize = 0x600b_0000;
        const PMU_HP_SLEEP_ICG_MODEM: usize = PMU_BASE + 0x74;
        const PMU_HP_MODEM_ICG_MODEM: usize = PMU_BASE + 0x40;
        const PMU_HP_ACTIVE_ICG_MODEM: usize = PMU_BASE + 0x0C;
        const ICG_MODEM_CODE_FIELD: u32 = 0b11 << 30; // bits[31:30]
        // sleep code = 0: just clear this field
        let v = read32(PMU_HP_SLEEP_ICG_MODEM);
        write32(PMU_HP_SLEEP_ICG_MODEM, v & !ICG_MODEM_CODE_FIELD);
        // modem code = 1
        let v = read32(PMU_HP_MODEM_ICG_MODEM);
        write32(PMU_HP_MODEM_ICG_MODEM, (v & !ICG_MODEM_CODE_FIELD) | (1 << 30));
        // active code = 2
        let v = read32(PMU_HP_ACTIVE_ICG_MODEM);
        write32(PMU_HP_ACTIVE_ICG_MODEM, (v & !ICG_MODEM_CODE_FIELD) | (2 << 30));

        // imm_modem_icg @ 0xDC: bit31 update_dig_icg_modem_en — setting 1 triggers the
        // above ICG codes to take effect immediately (PAC BitWriter start bit 31).
        // write-only trigger bit, just write 1<<31.
        const PMU_IMM_MODEM_ICG: usize = PMU_BASE + 0xDC;
        write32(PMU_IMM_MODEM_ICG, 1 << 31);

        // imm_sleep_sysclk @ 0xD0: bit28 update_dig_icg_switch — setting 1 triggers the
        // clock switch to take effect immediately (PAC BitWriter start bit 28; bits
        // 29/30/31 of the same register are other fields, only set bit28).
        const PMU_IMM_SLEEP_SYSCLK: usize = PMU_BASE + 0xD0;
        write32(PMU_IMM_SLEEP_SYSCLK, 1 << 28);

        // (2) power_st state mapping: map each modem sub-domain clock into the power
        // state machine's state map. Each *_st_map is a 4-bit field; value 6 means
        // "this clock is enabled in the corresponding power state".
        // MODEM_SYSCON.clk_conf_power_st @ 0x600A_980C (PAC offset 0x0C):
        //   clk_modem_apb_st_map  [31:28] = 6
        //   clk_modem_peri_st_map [27:24] = 4
        //   clk_wifi_st_map       [23:20] = 6
        //   clk_bt_st_map         [19:16] = 6
        //   clk_fe_st_map         [15:12] = 6
        //   clk_zb_st_map         [11:8]  = 6
        const MODEM_SYSCON_CLK_CONF_POWER_ST: usize = 0x600A_980C;
        // Low 8 bits [7:0] have no field, preserve original value; assign the high 24
        // bits as above. Direct assembly:
        //   apb=6<<28 | peri=4<<24 | wifi=6<<20 | bt=6<<16 | fe=6<<12 | zb=6<<8
        const SYSCON_POWER_ST_HI: u32 = (6 << 28) | (4 << 24) | (6 << 20)
            | (6 << 16) | (6 << 12) | (6 << 8);
        let lo = read32(MODEM_SYSCON_CLK_CONF_POWER_ST) & 0xFF;
        write32(MODEM_SYSCON_CLK_CONF_POWER_ST, SYSCON_POWER_ST_HI | lo);

        // MODEM_LPCON.clk_conf_power_st @ 0x600A_F020 (PAC offset 0x20):
        //   clk_lp_apb_st_map   [31:28] = 6
        //   clk_i2c_mst_st_map  [27:24] = 6
        //   clk_coex_st_map     [23:20] = 6
        //   clk_wifipwr_st_map  [19:16] = 6
        // Low 16 bits [15:0] have no field, preserve original value.
        const MODEM_LPCON_CLK_CONF_POWER_ST: usize = 0x600A_F020;
        const LPCON_POWER_ST_HI: u32 = (6 << 28) | (6 << 24) | (6 << 20) | (6 << 16);
        let lo = read32(MODEM_LPCON_CLK_CONF_POWER_ST) & 0xFFFF;
        write32(MODEM_LPCON_CLK_CONF_POWER_ST, LPCON_POWER_ST_HI | lo);

        // (3) WiFi low-power clock source: MODEM_LPCON.wifi_lp_clk_conf @ 0x600A_F00C
        // (PAC offset 0x0C). Set all 4 clock-source select bits (bit0 osc_slow |
        // bit1 osc_fast | bit2 xtal | bit3 xtal32k) selected (esp-radio sets all four
        // via set_bit) + clk_wifipwr_lp_div_num[15:4] = 0.
        // All sources selected + div=0 is the esp-idf/esp-radio default config for
        // the C6 wifipwr low-power clock.
        const MODEM_LPCON_WIFI_LP_CLK_CONF: usize = 0x600A_F00C;
        const LPCON_LP_CLK_SEL_MASK: u32 = 0b1111; // bit0-3 four sel bits
        const LPCON_LP_DIV_NUM_MASK: u32 = 0xFFF0; // bits[15:4] div_num
        let v = read32(MODEM_LPCON_WIFI_LP_CLK_CONF);
        // Clear div_num then set the 4 sel bits, preserving the rest
        write32(
            MODEM_LPCON_WIFI_LP_CLK_CONF,
            (v & !LPCON_LP_DIV_NUM_MASK) | LPCON_LP_CLK_SEL_MASK,
        );

        // Verification
        // regi2c_enif_init();
        // bbpll_calibrate();
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
