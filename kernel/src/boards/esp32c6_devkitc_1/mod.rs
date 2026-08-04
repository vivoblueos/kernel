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
const PLIC_MX_ENABLE: usize = PLIC_MX_BASE + 0x0;
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
const LP_WDT_CONFIG0: usize = LP_WDT_BASE + 0x00;
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

pub(crate) fn handle_intc_irq(ctx: &Context, mcause: usize, mtval: usize) {
    let _ = (ctx, mtval);
    match mcause & 0xff {
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

    unsafe {
        disable_wdt(LP_WDT_WPROTECT, LP_WDT_CONFIG0, 1 << 12);
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
