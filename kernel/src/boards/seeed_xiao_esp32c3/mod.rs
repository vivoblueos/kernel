// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
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
use crate::{
    arch,
    arch::riscv::{local_irq_enabled, trap_entry, Context},
    scheduler, time,
};
use blueos_driver::{
    interrupt_controller::Interrupt, power::esp32c3_power_domain::PowerDomain,
    uart::esp32_usb_serial::Esp32UsbSerialIsr,
};
use blueos_hal::{isr::IsrDesc, Has8bitDataReg};

// FIXME: Only support unit0 for now
pub type ClockImpl =
    blueos_driver::systimer::esp32_sys_timer::Esp32SysTimer<0x6002_3000, 16_000_000>;

pub type Spi2Impl =
    blueos_driver::spi::esp32_spi::Esp32Spi2<0x6002_4000, 0x600c_0000, 80_000_000>;

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

pub(crate) fn handle_intc_irq(ctx: &Context, mcause: usize, mtval: usize) {
    let cpu_id = arch::current_cpu_id();
    match mcause & 0xff {
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

const TARGET0_INT_NUM: usize = 16;

const USB_SERIAL_JTAG_INT_NUM: usize = 15;

const RTC_CNTL_BASE: usize = 0x6000_8000;
const RTC_CNTL_WDTWRITECT_REG: usize = RTC_CNTL_BASE + 0xA8;
const RTC_CNTL_WDTCONFIG0_REG: usize = RTC_CNTL_BASE + 0x90;

const USB_SERIAL_JTAG_IRQ: Interrupt = Interrupt::new(26, USB_SERIAL_JTAG_INT_NUM);
const SYSTIMER_TARGET0_IRQ: Interrupt = Interrupt::new(37, TARGET0_INT_NUM);

pub(crate) fn init() {
    assert!(!local_irq_enabled());

    crate::boot::init_runtime();
    crate::boot::init_heap();
    init_vector_table();

    blueos_driver::systimer::esp32_sys_timer::Esp32SysTimer::<0x6002_3000, 16_000_000>::init();

    unsafe {
        // disable WDT to avoid unexpected reset
        core::ptr::write_volatile(RTC_CNTL_WDTWRITECT_REG as *mut u32, 0x50D83AA1);
        core::ptr::write_volatile(RTC_CNTL_WDTCONFIG0_REG as *mut u32, 0);
        core::ptr::write_volatile(RTC_CNTL_WDTWRITECT_REG as *mut u32, 0);
    }

    get_device!(intc).allocate_irq(SYSTIMER_TARGET0_IRQ);
    get_device!(intc).allocate_irq(USB_SERIAL_JTAG_IRQ);

    get_device!(intc).set_threshold(1);

    get_device!(intc).set_priority(USB_SERIAL_JTAG_IRQ, 15);
    get_device!(intc).set_priority(SYSTIMER_TARGET0_IRQ, 15);
    get_device!(intc).enable_irq(SYSTIMER_TARGET0_IRQ);
    get_device!(intc).enable_irq(USB_SERIAL_JTAG_IRQ);

    let power_domain = PowerDomain::new(0x6000_8000);
    power_domain.enable_wifi();

    #[cfg(enable_net)]
    unsafe {
        use esp_wifi_sys_esp32c3::include::{
            esp_wifi_internal_set_log_level, wifi_log_level_t_WIFI_LOG_VERBOSE,
        };

        esp_wifi_internal_set_log_level(wifi_log_level_t_WIFI_LOG_VERBOSE);
    }

    unsafe {
        // open wifi clk
        // modified from https://github.com/esp-rs/esp-hal/blob/63ff86ca206fc1bd25699527ed30094f3bb9a872/esp-radio/src/radio_clocks/clocks_ll/esp32c3.rs#L35-L42
        const SYSTEM_WIFI_CLK_I2C_CLK_EN: u32 = 1 << 5;
        const SYSTEM_WIFI_CLK_UNUSED_BIT12: u32 = 1 << 12;
        const WIFI_BT_SDIO_CLK: u32 = SYSTEM_WIFI_CLK_I2C_CLK_EN | SYSTEM_WIFI_CLK_UNUSED_BIT12;
        let tmp = core::ptr::read_volatile(0x6002_6014 as *const u32);
        core::ptr::write_volatile(
            0x6002_6014 as *mut u32,
            tmp & !WIFI_BT_SDIO_CLK | 0x00FB9FCF,
        );
    }
}

crate::define_peripheral! {
    (console_uart, blueos_driver::uart::esp32_usb_serial::Esp32UsbSerial,
     blueos_driver::uart::esp32_usb_serial::Esp32UsbSerial::new()),
    (intc, blueos_driver::interrupt_controller::esp32_intc::Esp32Intc,
     blueos_driver::interrupt_controller::esp32_intc::Esp32Intc::new(0x600c_2000)),
    (spi2, Spi2Impl, Spi2Impl::new()),
    (flash_cs, blueos_driver::gpio::esp32_gpio::Esp32GpioOutputPin,
     blueos_driver::gpio::esp32_gpio::Esp32GpioOutputPin::new(5)),
}

crate::define_pin_states!(None);

crate::define_bus! {
    (spi2_bus, crate::devices::spi_core::block_spi::BlockSpi<Spi2Impl, blueos_driver::gpio::esp32_gpio::Esp32GpioOutputPin>,
        (flash, crate::drivers::flash::spi_flash::SpiFlashConfig,
            crate::drivers::flash::spi_flash::SpiFlashConfig::new(BLOCK_STORAGE_DEVICE_NAME)),
    )
}

pub const BLOCK_STORAGE_DEVICE_NAME: &str = "flash-storage";
pub const BLOCK_STORAGE_MOUNT_POINT: &str = "data";

#[cfg(spi_core)]
pub(crate) fn init_spi_bus() {
    use alloc::sync::Arc;
    use crate::devices::bus::Bus;
    use crate::devices::spi_core::block_spi::BlockSpi;
    use crate::drivers::InitDriver;
    use blueos_driver::{pinctrl::esp32_pinctrl::Esp32IoMuxPinctrl, spi::SpiConfig};
    use blueos_hal::pinctrl::AlterFuncPin;
    use spin::Once;

    // SPI2 pins: SCK=GPIO8, MISO=GPIO9, MOSI=GPIO10, CS=GPIO5.
    const PIN_STATES: [Esp32IoMuxPinctrl; 4] = [
        Esp32IoMuxPinctrl::new(8, 1, false, false, false, 2, Some(63), None, false), // SCK
        Esp32IoMuxPinctrl::new(9, 1, true, false, false, 2, None, Some(64), false),  // MISO
        Esp32IoMuxPinctrl::new(10, 1, false, false, false, 2, Some(65), None, false), // MOSI
        Esp32IoMuxPinctrl::new(5, 1, false, true, false, 2, None, None, true),       // CS
    ];
    for pin in PIN_STATES {
        pin.init();
    }

    static SPI2_BUS: Once<Arc<Bus<BlockSpi<Spi2Impl, blueos_driver::gpio::esp32_gpio::Esp32GpioOutputPin>>>> =
        Once::new();

    let spi2 = get_device!(spi2);
    let cs = get_device!(flash_cs);
    let block_spi = BlockSpi::new(spi2, cs, &SpiConfig::spi_flash_default())
        .expect("Failed to configure SPI2 for flash");
    SPI2_BUS.call_once(|| Arc::new(Bus::new(block_spi)));
    let spi2_bus = SPI2_BUS.get().unwrap();
    for device in crate::boards::get_bus_devices!(spi2_bus) {
        spi2_bus.register_device(device).unwrap();
    }
    if let Ok(d) = spi2_bus.probe_driver(&crate::drivers::flash::spi_flash::SpiFlashDriverModule) {
        if let Err(e) = d.init(spi2_bus) {
            log::warn!("Failed to init SPI flash: {}", e);
        }
    }
}

#[inline(always)]
pub(crate) fn send_ipi(_hart: usize) {}

#[inline(always)]
pub(crate) fn clear_ipi(_hart: usize) {}

static ESP32_USB_SERIAL_ISR: Esp32UsbSerialIsr<0x6004_3000, crate::drivers::serial::Serial> =
    Esp32UsbSerialIsr::<0x6004_3000, _> {
        data: &crate::drivers::serial::TTY_SERIAL,
        tx_isr: Some(crate::drivers::serial::Serial::xmitchars),
        rx_isr: Some(crate::drivers::serial::Serial::recvchars),
    };
