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
    arch,
    arch::irq::{InterruptTable, Vector, INTERRUPT_TABLE_LEN},
    boot::_start,
    time,
};

extern "C" {
    pub fn uart0rx_handler();
    pub fn uart0tx_handler();
}

#[no_mangle]
#[linkage = "weak"]
pub unsafe extern "C" fn uart1rx_handler() {
    unreachable!("Should not reach here");
}

#[no_mangle]
#[linkage = "weak"]
pub unsafe extern "C" fn uart1tx_handler() {
    unreachable!("Should not reach here");
}

unsafe extern "C" fn do_nothing() {}

unsafe extern "C" fn busy() {
    unreachable!("Should not be busy!");
}

#[no_mangle]
#[linkage = "weak"]
pub unsafe extern "C" fn bk_handle_hardfault() {
    arch::arm::handle_hardfault()
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
        handler: bk_handle_hardfault,
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
    tbl[10] = Vector {
        handler: arch::arm::handle_svc,
    };
    tbl[13] = Vector {
        handler: arch::arm::handle_pendsv,
    };
    tbl[14] = Vector {
        handler: super::handle_systick,
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
default_irq_handler!(uart2rx_handler);
default_irq_handler!(uart2tx_handler);
default_irq_handler!(gpio0all_handler);
default_irq_handler!(gpio1all_handler);
default_irq_handler!(timer0_handler);
default_irq_handler!(timer1_handler);
default_irq_handler!(dualtimer_handler);
default_irq_handler!(spi_0_1_handler);
default_irq_handler!(uart_0_1_2_ovf_handler);
default_irq_handler!(ethernet_handler);
default_irq_handler!(i2s_handler);
default_irq_handler!(touchscreen_handler);
default_irq_handler!(gpio2_handler);
default_irq_handler!(gpio3_handler);
default_irq_handler!(uart3rx_handler);
default_irq_handler!(uart3tx_handler);
default_irq_handler!(uart4rx_handler);
default_irq_handler!(uart4tx_handler);
default_irq_handler!(spi_2_handler);
default_irq_handler!(spi_3_4_handler);
default_irq_handler!(gpio0_0_handler);
default_irq_handler!(gpio0_1_handler);
default_irq_handler!(gpio0_2_handler);
default_irq_handler!(gpio0_3_handler);
default_irq_handler!(gpio0_4_handler);
default_irq_handler!(gpio0_5_handler);
default_irq_handler!(gpio0_6_handler);
default_irq_handler!(gpio0_7_handler);

#[used]
#[link_section = ".interrupt.handlers"]
#[no_mangle]
pub static __INTERRUPT_HANDLERS__: InterruptTable = {
    let mut tbl = [Vector { reserved: 0 }; INTERRUPT_TABLE_LEN];
    tbl[0] = Vector {
        handler: uart0rx_handler,
    };
    tbl[1] = Vector {
        handler: uart0tx_handler,
    };
    tbl[2] = Vector {
        handler: uart1rx_handler,
    };
    tbl[3] = Vector {
        handler: uart1tx_handler,
    };
    tbl[4] = Vector {
        handler: uart2rx_handler,
    };
    tbl[5] = Vector {
        handler: uart2tx_handler,
    };
    tbl[6] = Vector {
        handler: gpio0all_handler,
    };
    tbl[7] = Vector {
        handler: gpio1all_handler,
    };
    tbl[8] = Vector {
        handler: timer0_handler,
    };
    tbl[9] = Vector {
        handler: timer1_handler,
    };
    tbl[10] = Vector {
        handler: dualtimer_handler,
    };
    tbl[11] = Vector {
        handler: spi_0_1_handler,
    };
    tbl[12] = Vector {
        handler: uart_0_1_2_ovf_handler,
    };
    tbl[13] = Vector {
        handler: ethernet_handler,
    };
    tbl[14] = Vector {
        handler: i2s_handler,
    };
    tbl[15] = Vector {
        handler: touchscreen_handler,
    };
    tbl[16] = Vector {
        handler: gpio2_handler,
    };
    tbl[17] = Vector {
        handler: gpio3_handler,
    };
    tbl[18] = Vector {
        handler: uart3rx_handler,
    };
    tbl[19] = Vector {
        handler: uart3tx_handler,
    };
    tbl[20] = Vector {
        handler: uart4rx_handler,
    };
    tbl[21] = Vector {
        handler: uart4tx_handler,
    };
    tbl[22] = Vector {
        handler: spi_2_handler,
    };
    tbl[23] = Vector {
        handler: spi_3_4_handler,
    };
    tbl[24] = Vector {
        handler: gpio0_0_handler,
    };
    tbl[25] = Vector {
        handler: gpio0_1_handler,
    };
    tbl[26] = Vector {
        handler: gpio0_2_handler,
    };
    tbl[27] = Vector {
        handler: gpio0_3_handler,
    };
    tbl[28] = Vector {
        handler: gpio0_4_handler,
    };
    tbl[29] = Vector {
        handler: gpio0_5_handler,
    };
    tbl[30] = Vector {
        handler: gpio0_6_handler,
    };
    tbl[31] = Vector {
        handler: gpio0_7_handler,
    };
    tbl
};
