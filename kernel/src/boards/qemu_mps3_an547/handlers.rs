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

use crate::{
    arch::{
        self,
        irq::{InterruptTable, Vector, INTERRUPT_TABLE_LEN},
    },
    boot::_start,
    time,
};

unsafe extern "C" fn do_nothing() {}

unsafe extern "C" fn busy() {
    loop {}
}

#[used]
#[link_section = ".exception.handlers"]
#[no_mangle]
pub static __EXCEPTION_HANDLERS__: [Vector; 15] = build_exception_handlers();

// See https://documentation-service.arm.com/static/5ea823e69931941038df1b02?token=.
const fn build_exception_handlers() -> [Vector; 15] {
    let mut tbl = [Vector { reserved: 0 }; 15];
    tbl[0] = Vector { handler: _start };
    tbl[1] = Vector {
        handler: arch::arm::handle_hardfault,
    }; // NMI
    tbl[2] = Vector {
        handler: arch::arm::handle_hardfault,
    }; // HardFault
    tbl[3] = Vector {
        handler: arch::arm::handle_hardfault,
    }; // MemManage
    tbl[4] = Vector {
        handler: arch::arm::handle_hardfault,
    }; // BusFault
    tbl[5] = Vector {
        handler: arch::arm::handle_hardfault,
    }; // UsageFault
    tbl[6] = Vector {
        handler: arch::arm::handle_hardfault,
    }; // SecureFault
    tbl[10] = Vector {
        handler: arch::arm::handle_svc,
    };
    tbl[13] = Vector {
        handler: arch::arm::handle_pendsv,
    };
    tbl[14] = Vector {
        handler: time::handle_tick_increment,
    };
    tbl
}

macro_rules! default_irq_handler {
    ($handler_name:ident) => {
        unsafe extern "C" fn $handler_name() {
            $crate::debug!("{}", stringify!($handler_name));
        }
    };
}

use super::uart::{uart0rx_handler, uart0tx_handler};
default_irq_handler!(nonsec_watchdog_reset_req_handler);
default_irq_handler!(nonsec_watchdog_handler);
default_irq_handler!(slowclk_timer_handler);
default_irq_handler!(tfm_timer0_irq_handler);
default_irq_handler!(timer1_handler);
default_irq_handler!(timer2_handler);
default_irq_handler!(mpc_handler);
default_irq_handler!(ppc_handler);
default_irq_handler!(msc_handler);
default_irq_handler!(bridge_error_handler);
default_irq_handler!(mgmt_ppu_handler);
default_irq_handler!(sys_ppu_handler);
default_irq_handler!(cpu0_ppu_handler);
default_irq_handler!(debug_ppu_handler);
default_irq_handler!(timer3_aon_handler);
default_irq_handler!(cpu0_cti_0_handler);
default_irq_handler!(cpu0_cti_1_handler);
default_irq_handler!(system_timestamp_counter_handler);
default_irq_handler!(uartrx1_handler);
default_irq_handler!(uarttx1_handler);
default_irq_handler!(uartrx2_handler);
default_irq_handler!(uarttx2_handler);
default_irq_handler!(uartrx3_handler);
default_irq_handler!(uarttx3_handler);
default_irq_handler!(uartrx4_handler);
default_irq_handler!(uarttx4_handler);

#[doc(hidden)]
#[link_section = ".interrupt.handlers"]
#[no_mangle]
static __INTERRUPT_HANDLERS__: InterruptTable = {
    let mut tbl = [Vector { reserved: 0 }; INTERRUPT_TABLE_LEN];

    tbl[0] = Vector {
        handler: nonsec_watchdog_reset_req_handler,
    };
    tbl[1] = Vector {
        handler: nonsec_watchdog_handler,
    };
    tbl[2] = Vector {
        handler: slowclk_timer_handler,
    };
    tbl[3] = Vector {
        handler: tfm_timer0_irq_handler,
    };
    tbl[4] = Vector {
        handler: timer1_handler,
    };
    tbl[5] = Vector {
        handler: timer2_handler,
    };
    tbl[6] = Vector { reserved: 0 };
    tbl[7] = Vector { reserved: 0 };
    tbl[8] = Vector { reserved: 0 };
    tbl[9] = Vector {
        handler: mpc_handler,
    };
    tbl[10] = Vector {
        handler: ppc_handler,
    };
    tbl[11] = Vector {
        handler: msc_handler,
    };
    tbl[12] = Vector {
        handler: bridge_error_handler,
    };
    tbl[13] = Vector { reserved: 0 };
    tbl[14] = Vector {
        handler: mgmt_ppu_handler,
    };
    tbl[15] = Vector {
        handler: sys_ppu_handler,
    };
    tbl[16] = Vector {
        handler: cpu0_ppu_handler,
    };
    tbl[17] = Vector { reserved: 0 };
    tbl[18] = Vector { reserved: 0 };
    tbl[19] = Vector { reserved: 0 };
    tbl[20] = Vector { reserved: 0 };
    tbl[21] = Vector { reserved: 0 };
    tbl[22] = Vector { reserved: 0 };
    tbl[23] = Vector { reserved: 0 };
    tbl[24] = Vector { reserved: 0 };
    tbl[25] = Vector {
        handler: debug_ppu_handler,
    };
    tbl[27] = Vector {
        handler: timer3_aon_handler,
    };
    tbl[28] = Vector {
        handler: cpu0_cti_0_handler,
    };
    tbl[29] = Vector {
        handler: cpu0_cti_1_handler,
    };
    tbl[30] = Vector { reserved: 0 };
    tbl[31] = Vector { reserved: 0 };
    tbl[32] = Vector {
        handler: system_timestamp_counter_handler,
    };
    // In the new version of QEMU (9.20), the UART RX interrupt and TX interrupt have been swapped.
    // For details, see `fix RX/TX interrupts order <https://github.com/qemu/qemu/commit/5a558be93ad628e5bed6e0ee062870f49251725c>`_
    // default set as new version of QEMU
    tbl[33] = Vector {
        handler: uart0rx_handler,
    };
    tbl[34] = Vector {
        handler: uart0tx_handler,
    };
    tbl[35] = Vector {
        handler: uartrx1_handler,
    };
    tbl[36] = Vector {
        handler: uarttx1_handler,
    };
    tbl[37] = Vector {
        handler: uartrx2_handler,
    };
    tbl[38] = Vector {
        handler: uarttx2_handler,
    };
    tbl[39] = Vector {
        handler: uartrx3_handler,
    };
    tbl[40] = Vector {
        handler: uarttx3_handler,
    };
    tbl[41] = Vector {
        handler: uartrx4_handler,
    };
    tbl[42] = Vector {
        handler: uarttx4_handler,
    };

    tbl
};
