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

use blueos::{boards::qemu_mps2_an385::config, irq::IrqTrace, support::DisableInterruptGuard};

extern "C" {
    fn Interrupt2_Handler();
    fn Interrupt3_Handler();
}

// only used for CMSIS-RTOS2 validation, so an disable guard is enough
#[no_mangle]
pub unsafe extern "C" fn uart1rx_handler() {
    let _trace = IrqTrace::new(config::UART1RX_IRQn);
    let _dig = DisableInterruptGuard::new();
    Interrupt2_Handler()
}

#[no_mangle]
pub unsafe extern "C" fn uart1tx_handler() {
    let _trace = IrqTrace::new(config::UART1TX_IRQn);
    let _dig = DisableInterruptGuard::new();
    Interrupt3_Handler()
}
