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

use gd32e5::*;

pub struct Rcu {
    internal: &'static gd32e507::rcu::RegisterBlock,
}

#[derive(PartialEq)]
pub enum ClkSource {
    Irc8m,
    Hxtal,
    Pll,
    Reserved,
}

pub enum AhbPrescaling {
    None,
    Div2,
    Div4,
    Div8,
    Div16,
    Div64,
    Div128,
    Div256,
    Div512,
}

pub enum ApbPrescaling {
    None,
    Div2,
    Div4,
    Div8,
    Div16,
}

pub enum RcuPart {
    Pll,
    Ckm,
    Hxtal,
}

impl Rcu {
    pub fn new() -> Self {
        Rcu {
            internal: unsafe { &*gd32e507::Rcu::ptr() },
        }
    }

    pub fn wait_for_clock_stablized() {
        while unsafe { &*gd32e507::Rcu::ptr() }
            .ctl()
            .read()
            .irc8mstb()
            .bit_is_clear()
        {}
    }

    pub fn get_system_clk_source(&self) -> ClkSource {
        match self.internal.cfg0().read().scs().bits() {
            0b00 => ClkSource::Irc8m,
            0b01 => ClkSource::Hxtal,
            0b10 => ClkSource::Pll,
            _ => ClkSource::Reserved,
        }
    }

    pub fn select_system_clk_source(&self, source: ClkSource) {
        match source {
            ClkSource::Irc8m => {
                self.internal
                    .cfg0()
                    .modify(|_, w| unsafe { w.scs().bits(0b00) });
                while self.get_system_clk_source() != ClkSource::Irc8m {}
            }
            ClkSource::Hxtal => {
                self.internal
                    .cfg0()
                    .modify(|_, w| unsafe { w.scs().bits(0b01) });
                while self.get_system_clk_source() != ClkSource::Hxtal {}
            }
            ClkSource::Pll => {
                self.internal
                    .cfg0()
                    .modify(|_, w| unsafe { w.scs().bits(0b10) });
                while self.get_system_clk_source() != ClkSource::Pll {}
            }
            _ => {}
        }
    }

    pub fn set_ahb_prescaling(&self, prescale: AhbPrescaling) {
        match prescale {
            AhbPrescaling::None => {
                self.internal
                    .cfg0()
                    .modify(|_, w| unsafe { w.ahbpsc().bits(0b0000) });
            }
            AhbPrescaling::Div2 => {
                self.internal
                    .cfg0()
                    .modify(|_, w| unsafe { w.ahbpsc().bits(0b1000) });
            }
            AhbPrescaling::Div4 => {
                self.internal
                    .cfg0()
                    .modify(|_, w| unsafe { w.ahbpsc().bits(0b1001) });
            }
            AhbPrescaling::Div8 => {
                self.internal
                    .cfg0()
                    .modify(|_, w| unsafe { w.ahbpsc().bits(0b1010) });
            }
            AhbPrescaling::Div16 => {
                self.internal
                    .cfg0()
                    .modify(|_, w| unsafe { w.ahbpsc().bits(0b1011) });
            }
            AhbPrescaling::Div64 => {
                self.internal
                    .cfg0()
                    .modify(|_, w| unsafe { w.ahbpsc().bits(0b1100) });
            }
            AhbPrescaling::Div128 => {
                self.internal
                    .cfg0()
                    .modify(|_, w| unsafe { w.ahbpsc().bits(0b1101) });
            }
            AhbPrescaling::Div256 => {
                self.internal
                    .cfg0()
                    .modify(|_, w| unsafe { w.ahbpsc().bits(0b1110) });
            }
            AhbPrescaling::Div512 => {
                self.internal
                    .cfg0()
                    .modify(|_, w| unsafe { w.ahbpsc().bits(0b1111) });
            }
        }
    }

    pub fn set_abp1_prescaling(&self, prescale: ApbPrescaling) {
        match prescale {
            ApbPrescaling::None => {
                self.internal
                    .cfg0()
                    .modify(|_, w| unsafe { w.apb1psc().bits(0b000) });
            }
            ApbPrescaling::Div2 => {
                self.internal
                    .cfg0()
                    .modify(|_, w| unsafe { w.apb1psc().bits(0b100) });
            }
            ApbPrescaling::Div4 => {
                self.internal
                    .cfg0()
                    .modify(|_, w| unsafe { w.apb1psc().bits(0b101) });
            }
            ApbPrescaling::Div8 => {
                self.internal
                    .cfg0()
                    .modify(|_, w| unsafe { w.apb1psc().bits(0b110) });
            }
            ApbPrescaling::Div16 => {
                self.internal
                    .cfg0()
                    .modify(|_, w| unsafe { w.apb1psc().bits(0b111) });
            }
        }
    }

    pub fn set_abp2_prescaling(&self, prescale: ApbPrescaling) {
        match prescale {
            ApbPrescaling::None => {
                self.internal
                    .cfg0()
                    .modify(|_, w| unsafe { w.apb2psc().bits(0b000) });
            }
            ApbPrescaling::Div2 => {
                self.internal
                    .cfg0()
                    .modify(|_, w| unsafe { w.apb2psc().bits(0b100) });
            }
            ApbPrescaling::Div4 => {
                self.internal
                    .cfg0()
                    .modify(|_, w| unsafe { w.apb2psc().bits(0b101) });
            }
            ApbPrescaling::Div8 => {
                self.internal
                    .cfg0()
                    .modify(|_, w| unsafe { w.apb2psc().bits(0b110) });
            }
            ApbPrescaling::Div16 => {
                self.internal
                    .cfg0()
                    .modify(|_, w| unsafe { w.apb2psc().bits(0b111) });
            }
        }
    }

    pub fn clear_rcu_part(&self, part: RcuPart) {
        match part {
            RcuPart::Pll => {
                self.internal.ctl().modify(|_, w| w.pllen().clear_bit());
            }
            RcuPart::Ckm => {
                self.internal.ctl().modify(|_, w| w.ckmen().clear_bit());
            }
            RcuPart::Hxtal => {
                self.internal.ctl().modify(|_, w| w.hxtalen().clear_bit());
            }
        }
    }

    pub fn disable_rcu_int(&self) {
        self.internal
            .int()
            .write(|w| unsafe { w.bits(0x009f_0000) });
    }

    pub fn reset_cfg(&self) {
        self.internal
            .cfg0()
            .write(|w| unsafe { w.bits(0x0000_0000) });
        self.internal
            .cfg1()
            .write(|w| unsafe { w.bits(0x0000_0000) });
    }

    pub fn reset_hxtalbps(&self) {
        self.internal
            .ctl()
            .write(|w| unsafe { w.hxtalbps().clear_bit() });
    }

    pub fn set_system_clk_180m_irc8m(&self) {
        unsafe {
            (*gd32e507::Fmc::ptr())
                .ws()
                .modify(|_, w| w.wscnt().bits(4));
        }

        self.internal.apb1en().modify(|_, w| w.pmuen().set_bit());

        // AHB = SYSCLK
        self.set_ahb_prescaling(AhbPrescaling::None);
        // APB2 = AHB/1
        self.set_abp2_prescaling(ApbPrescaling::None);
        // APB1 = AHB/2
        self.set_abp1_prescaling(ApbPrescaling::Div2);
        // CK_PLL = (CK_IRC8M/2) * 45 = 180MHz
        self.internal
            .cfg0()
            .modify(|_, w| unsafe { w.pllmf_3_0().bits(12) });
        self.internal
            .cfg0()
            .modify(|_, w| unsafe { w.pllmf_5_4().bits(0b10) });

        self.internal.ctl().modify(|_, w| w.pllen().set_bit());

        while self.internal.ctl().read().pllstb().bit_is_clear() {}

        unsafe { &*gd32e507::Pmu::ptr() }
            .ctl0()
            .modify(|_, w| w.hden().set_bit());

        while unsafe { &*gd32e507::Pmu::ptr() }
            .cs0()
            .read()
            .hdrf()
            .bit_is_clear()
        {}

        unsafe { &*gd32e507::Pmu::ptr() }
            .ctl0()
            .modify(|_, w| w.hds().set_bit());

        while unsafe { &*gd32e507::Pmu::ptr() }
            .cs0()
            .read()
            .hdsrf()
            .bit_is_clear()
        {}

        self.select_system_clk_source(ClkSource::Pll);

        while self.get_system_clk_source() != ClkSource::Pll {}
    }
}

unsafe fn enable_fpu() {
    const SCB_CPACR_PTR: *mut u32 = 0xE000_ED88 as *mut u32;
    const SCB_CPACR_FULL_ACCESS: u32 = 0b11;
    let mut temp = SCB_CPACR_PTR.read_volatile();
    temp |= SCB_CPACR_FULL_ACCESS << (4 * 2);
    temp |= 0x00F00000;
    SCB_CPACR_PTR.write_volatile(temp);
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

pub unsafe fn init_soc() {
    enable_fpu();

    let rcu = Rcu::new();
    if rcu.get_system_clk_source() == ClkSource::Pll {
        rcu.set_ahb_prescaling(AhbPrescaling::Div4);
    }
    for i in 0..0x100 {
        continue;
    }
    rcu.select_system_clk_source(ClkSource::Pll);
    for i in 0..1000 {
        continue;
    }
    rcu.clear_rcu_part(RcuPart::Ckm);
    rcu.clear_rcu_part(RcuPart::Hxtal);
    rcu.clear_rcu_part(RcuPart::Pll);

    rcu.disable_rcu_int();

    rcu.reset_cfg();

    rcu.reset_hxtalbps();

    rcu.set_system_clk_180m_irc8m();

    unsafe {
        (*gd32e5::gd32e507::Rcu::ptr())
            .apb2en()
            .modify(|_, w| w.usart0en().set_bit());
        (*gd32e5::gd32e507::Rcu::ptr())
            .apb2en()
            .modify(|_, w| w.paen().set_bit());
    }
}
