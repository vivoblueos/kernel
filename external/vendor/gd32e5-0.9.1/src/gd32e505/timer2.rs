#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    ctl0: Ctl0,
    ctl1: Ctl1,
    smcfg: Smcfg,
    dmainten: Dmainten,
    intf: Intf,
    swevg: Swevg,
    _reserved_6_chctl0: [u8; 0x04],
    _reserved_7_chctl1: [u8; 0x04],
    chctl2: Chctl2,
    cnt: Cnt,
    psc: Psc,
    car: Car,
    _reserved12: [u8; 0x04],
    ch0cv: Ch0cv,
    ch1cv: Ch1cv,
    ch2cv: Ch2cv,
    ch3cv: Ch3cv,
    _reserved16: [u8; 0x04],
    dmacfg: Dmacfg,
    dmatb: Dmatb,
    _reserved18: [u8; 0xac],
    cfg: Cfg,
}
impl RegisterBlock {
    #[doc = "0x00 - control register 0"]
    #[inline(always)]
    pub const fn ctl0(&self) -> &Ctl0 {
        &self.ctl0
    }
    #[doc = "0x04 - control register 1"]
    #[inline(always)]
    pub const fn ctl1(&self) -> &Ctl1 {
        &self.ctl1
    }
    #[doc = "0x08 - slave mode control register"]
    #[inline(always)]
    pub const fn smcfg(&self) -> &Smcfg {
        &self.smcfg
    }
    #[doc = "0x0c - DMA/Interrupt enable register"]
    #[inline(always)]
    pub const fn dmainten(&self) -> &Dmainten {
        &self.dmainten
    }
    #[doc = "0x10 - interrupt flag register"]
    #[inline(always)]
    pub const fn intf(&self) -> &Intf {
        &self.intf
    }
    #[doc = "0x14 - event generation register"]
    #[inline(always)]
    pub const fn swevg(&self) -> &Swevg {
        &self.swevg
    }
    #[doc = "0x18 - Channel control register 0 (input mode)"]
    #[inline(always)]
    pub const fn chctl0_input(&self) -> &Chctl0Input {
        unsafe { &*(self as *const Self).cast::<u8>().add(24).cast() }
    }
    #[doc = "0x18 - Channel control register 0 (output mode)"]
    #[inline(always)]
    pub const fn chctl0_output(&self) -> &Chctl0Output {
        unsafe { &*(self as *const Self).cast::<u8>().add(24).cast() }
    }
    #[doc = "0x1c - Channel control register 1 (input mode)"]
    #[inline(always)]
    pub const fn chctl1_input(&self) -> &Chctl1Input {
        unsafe { &*(self as *const Self).cast::<u8>().add(28).cast() }
    }
    #[doc = "0x1c - Channel control register 1 (output mode)"]
    #[inline(always)]
    pub const fn chctl1_output(&self) -> &Chctl1Output {
        unsafe { &*(self as *const Self).cast::<u8>().add(28).cast() }
    }
    #[doc = "0x20 - Channel control register 2"]
    #[inline(always)]
    pub const fn chctl2(&self) -> &Chctl2 {
        &self.chctl2
    }
    #[doc = "0x24 - Counter register"]
    #[inline(always)]
    pub const fn cnt(&self) -> &Cnt {
        &self.cnt
    }
    #[doc = "0x28 - Prescaler register"]
    #[inline(always)]
    pub const fn psc(&self) -> &Psc {
        &self.psc
    }
    #[doc = "0x2c - Counter auto reload register"]
    #[inline(always)]
    pub const fn car(&self) -> &Car {
        &self.car
    }
    #[doc = "0x34 - Channel 0 capture/compare value register"]
    #[inline(always)]
    pub const fn ch0cv(&self) -> &Ch0cv {
        &self.ch0cv
    }
    #[doc = "0x38 - Channel 1 capture/compare value register"]
    #[inline(always)]
    pub const fn ch1cv(&self) -> &Ch1cv {
        &self.ch1cv
    }
    #[doc = "0x3c - Channel 2 capture/compare value register"]
    #[inline(always)]
    pub const fn ch2cv(&self) -> &Ch2cv {
        &self.ch2cv
    }
    #[doc = "0x40 - Channel 3 capture/compare value register"]
    #[inline(always)]
    pub const fn ch3cv(&self) -> &Ch3cv {
        &self.ch3cv
    }
    #[doc = "0x48 - DMA configuration register"]
    #[inline(always)]
    pub const fn dmacfg(&self) -> &Dmacfg {
        &self.dmacfg
    }
    #[doc = "0x4c - DMA transfer buffer register"]
    #[inline(always)]
    pub const fn dmatb(&self) -> &Dmatb {
        &self.dmatb
    }
    #[doc = "0xfc - Configuration"]
    #[inline(always)]
    pub const fn cfg(&self) -> &Cfg {
        &self.cfg
    }
}
#[doc = "CTL0 (rw) register accessor: control register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ctl0`]
module"]
#[doc(alias = "CTL0")]
pub type Ctl0 = crate::Reg<ctl0::Ctl0Spec>;
#[doc = "control register 0"]
pub mod ctl0;
#[doc = "CTL1 (rw) register accessor: control register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ctl1`]
module"]
#[doc(alias = "CTL1")]
pub type Ctl1 = crate::Reg<ctl1::Ctl1Spec>;
#[doc = "control register 1"]
pub mod ctl1;
#[doc = "SMCFG (rw) register accessor: slave mode control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`smcfg::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`smcfg::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@smcfg`]
module"]
#[doc(alias = "SMCFG")]
pub type Smcfg = crate::Reg<smcfg::SmcfgSpec>;
#[doc = "slave mode control register"]
pub mod smcfg;
#[doc = "DMAINTEN (rw) register accessor: DMA/Interrupt enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dmainten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dmainten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dmainten`]
module"]
#[doc(alias = "DMAINTEN")]
pub type Dmainten = crate::Reg<dmainten::DmaintenSpec>;
#[doc = "DMA/Interrupt enable register"]
pub mod dmainten;
#[doc = "INTF (rw) register accessor: interrupt flag register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`intf::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`intf::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@intf`]
module"]
#[doc(alias = "INTF")]
pub type Intf = crate::Reg<intf::IntfSpec>;
#[doc = "interrupt flag register"]
pub mod intf;
#[doc = "SWEVG (w) register accessor: event generation register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`swevg::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@swevg`]
module"]
#[doc(alias = "SWEVG")]
pub type Swevg = crate::Reg<swevg::SwevgSpec>;
#[doc = "event generation register"]
pub mod swevg;
#[doc = "CHCTL0_Output (rw) register accessor: Channel control register 0 (output mode)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`chctl0_output::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`chctl0_output::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@chctl0_output`]
module"]
#[doc(alias = "CHCTL0_Output")]
pub type Chctl0Output = crate::Reg<chctl0_output::Chctl0OutputSpec>;
#[doc = "Channel control register 0 (output mode)"]
pub mod chctl0_output;
#[doc = "CHCTL0_Input (rw) register accessor: Channel control register 0 (input mode)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`chctl0_input::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`chctl0_input::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@chctl0_input`]
module"]
#[doc(alias = "CHCTL0_Input")]
pub type Chctl0Input = crate::Reg<chctl0_input::Chctl0InputSpec>;
#[doc = "Channel control register 0 (input mode)"]
pub mod chctl0_input;
#[doc = "CHCTL1_Output (rw) register accessor: Channel control register 1 (output mode)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`chctl1_output::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`chctl1_output::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@chctl1_output`]
module"]
#[doc(alias = "CHCTL1_Output")]
pub type Chctl1Output = crate::Reg<chctl1_output::Chctl1OutputSpec>;
#[doc = "Channel control register 1 (output mode)"]
pub mod chctl1_output;
#[doc = "CHCTL1_Input (rw) register accessor: Channel control register 1 (input mode)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`chctl1_input::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`chctl1_input::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@chctl1_input`]
module"]
#[doc(alias = "CHCTL1_Input")]
pub type Chctl1Input = crate::Reg<chctl1_input::Chctl1InputSpec>;
#[doc = "Channel control register 1 (input mode)"]
pub mod chctl1_input;
#[doc = "CHCTL2 (rw) register accessor: Channel control register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`chctl2::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`chctl2::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@chctl2`]
module"]
#[doc(alias = "CHCTL2")]
pub type Chctl2 = crate::Reg<chctl2::Chctl2Spec>;
#[doc = "Channel control register 2"]
pub mod chctl2;
#[doc = "CNT (rw) register accessor: Counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`cnt::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cnt::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cnt`]
module"]
#[doc(alias = "CNT")]
pub type Cnt = crate::Reg<cnt::CntSpec>;
#[doc = "Counter register"]
pub mod cnt;
#[doc = "PSC (rw) register accessor: Prescaler register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`psc::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`psc::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@psc`]
module"]
#[doc(alias = "PSC")]
pub type Psc = crate::Reg<psc::PscSpec>;
#[doc = "Prescaler register"]
pub mod psc;
#[doc = "CAR (rw) register accessor: Counter auto reload register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`car::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`car::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@car`]
module"]
#[doc(alias = "CAR")]
pub type Car = crate::Reg<car::CarSpec>;
#[doc = "Counter auto reload register"]
pub mod car;
#[doc = "CH0CV (rw) register accessor: Channel 0 capture/compare value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch0cv::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch0cv::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch0cv`]
module"]
#[doc(alias = "CH0CV")]
pub type Ch0cv = crate::Reg<ch0cv::Ch0cvSpec>;
#[doc = "Channel 0 capture/compare value register"]
pub mod ch0cv;
#[doc = "CH1CV (rw) register accessor: Channel 1 capture/compare value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch1cv::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch1cv::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch1cv`]
module"]
#[doc(alias = "CH1CV")]
pub type Ch1cv = crate::Reg<ch1cv::Ch1cvSpec>;
#[doc = "Channel 1 capture/compare value register"]
pub mod ch1cv;
#[doc = "CH2CV (rw) register accessor: Channel 2 capture/compare value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch2cv::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch2cv::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch2cv`]
module"]
#[doc(alias = "CH2CV")]
pub type Ch2cv = crate::Reg<ch2cv::Ch2cvSpec>;
#[doc = "Channel 2 capture/compare value register"]
pub mod ch2cv;
#[doc = "CH3CV (rw) register accessor: Channel 3 capture/compare value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch3cv::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch3cv::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch3cv`]
module"]
#[doc(alias = "CH3CV")]
pub type Ch3cv = crate::Reg<ch3cv::Ch3cvSpec>;
#[doc = "Channel 3 capture/compare value register"]
pub mod ch3cv;
#[doc = "DMACFG (rw) register accessor: DMA configuration register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dmacfg::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dmacfg::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dmacfg`]
module"]
#[doc(alias = "DMACFG")]
pub type Dmacfg = crate::Reg<dmacfg::DmacfgSpec>;
#[doc = "DMA configuration register"]
pub mod dmacfg;
#[doc = "DMATB (rw) register accessor: DMA transfer buffer register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dmatb::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dmatb::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dmatb`]
module"]
#[doc(alias = "DMATB")]
pub type Dmatb = crate::Reg<dmatb::DmatbSpec>;
#[doc = "DMA transfer buffer register"]
pub mod dmatb;
#[doc = "CFG (rw) register accessor: Configuration\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`cfg::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cfg::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
#[doc(alias = "CFG")]
pub type Cfg = crate::Reg<cfg::CfgSpec>;
#[doc = "Configuration"]
pub mod cfg;
