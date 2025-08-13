// Copyright (c) 2025 vivo Mobile Communication Co., Ltd.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::{
    arch::{self, irq::Vector},
    boot::_start,
    time,
};

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

use super::rp235x::uart::uart0_handler;

#[doc(hidden)]
#[link_section = ".interrupt.handlers"]
#[no_mangle]
static __INTERRUPT_HANDLERS__: [Vector; 50] = {
    let mut tbl = [Vector { reserved: 0 }; 50];
    tbl[33] = Vector {
        handler: uart0_handler,
    };
    tbl
};
