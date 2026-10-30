#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    st0ctl0: St0ctl0,
    st0intf: St0intf,
    st0intc: St0intc,
    st0dmainten: St0dmainten,
    st0cnt: St0cnt,
    st0car: St0car,
    st0crep: St0crep,
    st0cmp0v: St0cmp0v,
    st0cmp0cp: St0cmp0cp,
    st0cmp1v: St0cmp1v,
    st0cmp2v: St0cmp2v,
    st0cmp3v: St0cmp3v,
    st0cap0v: St0cap0v,
    st0cap1v: St0cap1v,
    st0dtctl: St0dtctl,
    st0ch0set: St0ch0set,
    st0ch0rst: St0ch0rst,
    st0ch1set: St0ch1set,
    st0ch1rst: St0ch1rst,
    st0exevfcfg0: St0exevfcfg0,
    st0exevfcfg1: St0exevfcfg1,
    st0cntrst: St0cntrst,
    st0csctl: St0csctl,
    st0cap0trg: St0cap0trg,
    st0cap1trg: St0cap1trg,
    st0choctl: St0choctl,
    st0fltctl: St0fltctl,
    _reserved27: [u8; 0x10],
    st0actl: St0actl,
}
impl RegisterBlock {
    #[doc = "0x00 - SHRTIMER Slave_TIMER0 control register 0"]
    #[inline(always)]
    pub const fn st0ctl0(&self) -> &St0ctl0 {
        &self.st0ctl0
    }
    #[doc = "0x04 - SHRTIMER Slave_TIMER0 interrupt flag register"]
    #[inline(always)]
    pub const fn st0intf(&self) -> &St0intf {
        &self.st0intf
    }
    #[doc = "0x08 - SHRTIMER Slave_TIMER0 interrupt flag clear register"]
    #[inline(always)]
    pub const fn st0intc(&self) -> &St0intc {
        &self.st0intc
    }
    #[doc = "0x0c - SHRTIMER Slave_TIMER0 DMA and interrupt enable register"]
    #[inline(always)]
    pub const fn st0dmainten(&self) -> &St0dmainten {
        &self.st0dmainten
    }
    #[doc = "0x10 - SHRTIMER Slave_TIMER0 counter register"]
    #[inline(always)]
    pub const fn st0cnt(&self) -> &St0cnt {
        &self.st0cnt
    }
    #[doc = "0x14 - SHRTIMER Slave_TIMER0 counter auto reload register"]
    #[inline(always)]
    pub const fn st0car(&self) -> &St0car {
        &self.st0car
    }
    #[doc = "0x18 - SHRTIMER Slave_TIMER0 counter repetition register"]
    #[inline(always)]
    pub const fn st0crep(&self) -> &St0crep {
        &self.st0crep
    }
    #[doc = "0x1c - SHRTIMER Slave_TIMER0 compare 0 value register"]
    #[inline(always)]
    pub const fn st0cmp0v(&self) -> &St0cmp0v {
        &self.st0cmp0v
    }
    #[doc = "0x20 - SHRTIMER Slave_TIMER0 compare 0 composite register"]
    #[inline(always)]
    pub const fn st0cmp0cp(&self) -> &St0cmp0cp {
        &self.st0cmp0cp
    }
    #[doc = "0x24 - SHRTIMER Slave_TIMER0 compare 1 value register"]
    #[inline(always)]
    pub const fn st0cmp1v(&self) -> &St0cmp1v {
        &self.st0cmp1v
    }
    #[doc = "0x28 - SHRTIMER Slave_TIMER0 compare 2 value register"]
    #[inline(always)]
    pub const fn st0cmp2v(&self) -> &St0cmp2v {
        &self.st0cmp2v
    }
    #[doc = "0x2c - SHRTIMER Slave_TIMER0 compare 3 value register"]
    #[inline(always)]
    pub const fn st0cmp3v(&self) -> &St0cmp3v {
        &self.st0cmp3v
    }
    #[doc = "0x30 - SHRTIMER Slave_TIMER0 capture 0 value register"]
    #[inline(always)]
    pub const fn st0cap0v(&self) -> &St0cap0v {
        &self.st0cap0v
    }
    #[doc = "0x34 - SHRTIMER Slave_TIMER0 capture 1 value register"]
    #[inline(always)]
    pub const fn st0cap1v(&self) -> &St0cap1v {
        &self.st0cap1v
    }
    #[doc = "0x38 - SHRTIMER Slave_TIMER0 dead-time control register"]
    #[inline(always)]
    pub const fn st0dtctl(&self) -> &St0dtctl {
        &self.st0dtctl
    }
    #[doc = "0x3c - SHRTIMER Slave_TIMERx channel 0 set request register"]
    #[inline(always)]
    pub const fn st0ch0set(&self) -> &St0ch0set {
        &self.st0ch0set
    }
    #[doc = "0x40 - SHRTIMER Slave_TIMER0 channel 0 reset request register"]
    #[inline(always)]
    pub const fn st0ch0rst(&self) -> &St0ch0rst {
        &self.st0ch0rst
    }
    #[doc = "0x44 - SHRTIMER Slave_TIMER0 channel 1 set request register"]
    #[inline(always)]
    pub const fn st0ch1set(&self) -> &St0ch1set {
        &self.st0ch1set
    }
    #[doc = "0x48 - SHRTIMER Slave_TIMER0 channel 1 reset request register"]
    #[inline(always)]
    pub const fn st0ch1rst(&self) -> &St0ch1rst {
        &self.st0ch1rst
    }
    #[doc = "0x4c - SHRTIMER Slave_TIMERx external event filter configuration register 0"]
    #[inline(always)]
    pub const fn st0exevfcfg0(&self) -> &St0exevfcfg0 {
        &self.st0exevfcfg0
    }
    #[doc = "0x50 - SHRTIMER Slave_TIMERx external event filter configuration register 1"]
    #[inline(always)]
    pub const fn st0exevfcfg1(&self) -> &St0exevfcfg1 {
        &self.st0exevfcfg1
    }
    #[doc = "0x54 - SHRTIMER Slave_TIMER0 counter reset register"]
    #[inline(always)]
    pub const fn st0cntrst(&self) -> &St0cntrst {
        &self.st0cntrst
    }
    #[doc = "0x58 - SHRTIMER Slave_TIMERx carrier-signal control register"]
    #[inline(always)]
    pub const fn st0csctl(&self) -> &St0csctl {
        &self.st0csctl
    }
    #[doc = "0x5c - SHRTIMER Slave_TIMER0 capture 0 trigger register"]
    #[inline(always)]
    pub const fn st0cap0trg(&self) -> &St0cap0trg {
        &self.st0cap0trg
    }
    #[doc = "0x60 - SHRTIMER Slave_TIMER0 capture 1 trigger register"]
    #[inline(always)]
    pub const fn st0cap1trg(&self) -> &St0cap1trg {
        &self.st0cap1trg
    }
    #[doc = "0x64 - SHRTIMER Slave_TIMERx channel output control register"]
    #[inline(always)]
    pub const fn st0choctl(&self) -> &St0choctl {
        &self.st0choctl
    }
    #[doc = "0x68 - SHRTIMER Slave_TIMERx fault control register"]
    #[inline(always)]
    pub const fn st0fltctl(&self) -> &St0fltctl {
        &self.st0fltctl
    }
    #[doc = "0x7c - SHRTIMER Slave_TIMERx additional control register"]
    #[inline(always)]
    pub const fn st0actl(&self) -> &St0actl {
        &self.st0actl
    }
}
#[doc = "ST0CTL0 (rw) register accessor: SHRTIMER Slave_TIMER0 control register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0ctl0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0ctl0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0ctl0`]
module"]
#[doc(alias = "ST0CTL0")]
pub type St0ctl0 = crate::Reg<st0ctl0::St0ctl0Spec>;
#[doc = "SHRTIMER Slave_TIMER0 control register 0"]
pub mod st0ctl0;
#[doc = "ST0INTF (r) register accessor: SHRTIMER Slave_TIMER0 interrupt flag register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0intf::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0intf`]
module"]
#[doc(alias = "ST0INTF")]
pub type St0intf = crate::Reg<st0intf::St0intfSpec>;
#[doc = "SHRTIMER Slave_TIMER0 interrupt flag register"]
pub mod st0intf;
#[doc = "ST0INTC (w) register accessor: SHRTIMER Slave_TIMER0 interrupt flag clear register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0intc::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0intc`]
module"]
#[doc(alias = "ST0INTC")]
pub type St0intc = crate::Reg<st0intc::St0intcSpec>;
#[doc = "SHRTIMER Slave_TIMER0 interrupt flag clear register"]
pub mod st0intc;
#[doc = "ST0DMAINTEN (rw) register accessor: SHRTIMER Slave_TIMER0 DMA and interrupt enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0dmainten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0dmainten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0dmainten`]
module"]
#[doc(alias = "ST0DMAINTEN")]
pub type St0dmainten = crate::Reg<st0dmainten::St0dmaintenSpec>;
#[doc = "SHRTIMER Slave_TIMER0 DMA and interrupt enable register"]
pub mod st0dmainten;
#[doc = "ST0CNT (rw) register accessor: SHRTIMER Slave_TIMER0 counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0cnt::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0cnt::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0cnt`]
module"]
#[doc(alias = "ST0CNT")]
pub type St0cnt = crate::Reg<st0cnt::St0cntSpec>;
#[doc = "SHRTIMER Slave_TIMER0 counter register"]
pub mod st0cnt;
#[doc = "ST0CAR (rw) register accessor: SHRTIMER Slave_TIMER0 counter auto reload register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0car::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0car::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0car`]
module"]
#[doc(alias = "ST0CAR")]
pub type St0car = crate::Reg<st0car::St0carSpec>;
#[doc = "SHRTIMER Slave_TIMER0 counter auto reload register"]
pub mod st0car;
#[doc = "ST0CREP (rw) register accessor: SHRTIMER Slave_TIMER0 counter repetition register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0crep::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0crep::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0crep`]
module"]
#[doc(alias = "ST0CREP")]
pub type St0crep = crate::Reg<st0crep::St0crepSpec>;
#[doc = "SHRTIMER Slave_TIMER0 counter repetition register"]
pub mod st0crep;
#[doc = "ST0CMP0V (rw) register accessor: SHRTIMER Slave_TIMER0 compare 0 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0cmp0v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0cmp0v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0cmp0v`]
module"]
#[doc(alias = "ST0CMP0V")]
pub type St0cmp0v = crate::Reg<st0cmp0v::St0cmp0vSpec>;
#[doc = "SHRTIMER Slave_TIMER0 compare 0 value register"]
pub mod st0cmp0v;
#[doc = "ST0CMP0CP (rw) register accessor: SHRTIMER Slave_TIMER0 compare 0 composite register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0cmp0cp::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0cmp0cp::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0cmp0cp`]
module"]
#[doc(alias = "ST0CMP0CP")]
pub type St0cmp0cp = crate::Reg<st0cmp0cp::St0cmp0cpSpec>;
#[doc = "SHRTIMER Slave_TIMER0 compare 0 composite register"]
pub mod st0cmp0cp;
#[doc = "ST0CMP1V (rw) register accessor: SHRTIMER Slave_TIMER0 compare 1 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0cmp1v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0cmp1v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0cmp1v`]
module"]
#[doc(alias = "ST0CMP1V")]
pub type St0cmp1v = crate::Reg<st0cmp1v::St0cmp1vSpec>;
#[doc = "SHRTIMER Slave_TIMER0 compare 1 value register"]
pub mod st0cmp1v;
#[doc = "ST0CMP2V (rw) register accessor: SHRTIMER Slave_TIMER0 compare 2 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0cmp2v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0cmp2v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0cmp2v`]
module"]
#[doc(alias = "ST0CMP2V")]
pub type St0cmp2v = crate::Reg<st0cmp2v::St0cmp2vSpec>;
#[doc = "SHRTIMER Slave_TIMER0 compare 2 value register"]
pub mod st0cmp2v;
#[doc = "ST0CMP3V (rw) register accessor: SHRTIMER Slave_TIMER0 compare 3 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0cmp3v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0cmp3v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0cmp3v`]
module"]
#[doc(alias = "ST0CMP3V")]
pub type St0cmp3v = crate::Reg<st0cmp3v::St0cmp3vSpec>;
#[doc = "SHRTIMER Slave_TIMER0 compare 3 value register"]
pub mod st0cmp3v;
#[doc = "ST0CAP0V (rw) register accessor: SHRTIMER Slave_TIMER0 capture 0 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0cap0v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0cap0v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0cap0v`]
module"]
#[doc(alias = "ST0CAP0V")]
pub type St0cap0v = crate::Reg<st0cap0v::St0cap0vSpec>;
#[doc = "SHRTIMER Slave_TIMER0 capture 0 value register"]
pub mod st0cap0v;
#[doc = "ST0CAP1V (rw) register accessor: SHRTIMER Slave_TIMER0 capture 1 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0cap1v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0cap1v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0cap1v`]
module"]
#[doc(alias = "ST0CAP1V")]
pub type St0cap1v = crate::Reg<st0cap1v::St0cap1vSpec>;
#[doc = "SHRTIMER Slave_TIMER0 capture 1 value register"]
pub mod st0cap1v;
#[doc = "ST0DTCTL (rw) register accessor: SHRTIMER Slave_TIMER0 dead-time control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0dtctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0dtctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0dtctl`]
module"]
#[doc(alias = "ST0DTCTL")]
pub type St0dtctl = crate::Reg<st0dtctl::St0dtctlSpec>;
#[doc = "SHRTIMER Slave_TIMER0 dead-time control register"]
pub mod st0dtctl;
#[doc = "ST0CH0SET (rw) register accessor: SHRTIMER Slave_TIMERx channel 0 set request register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0ch0set::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0ch0set::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0ch0set`]
module"]
#[doc(alias = "ST0CH0SET")]
pub type St0ch0set = crate::Reg<st0ch0set::St0ch0setSpec>;
#[doc = "SHRTIMER Slave_TIMERx channel 0 set request register"]
pub mod st0ch0set;
#[doc = "ST0CH0RST (rw) register accessor: SHRTIMER Slave_TIMER0 channel 0 reset request register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0ch0rst::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0ch0rst::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0ch0rst`]
module"]
#[doc(alias = "ST0CH0RST")]
pub type St0ch0rst = crate::Reg<st0ch0rst::St0ch0rstSpec>;
#[doc = "SHRTIMER Slave_TIMER0 channel 0 reset request register"]
pub mod st0ch0rst;
#[doc = "ST0CH1SET (rw) register accessor: SHRTIMER Slave_TIMER0 channel 1 set request register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0ch1set::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0ch1set::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0ch1set`]
module"]
#[doc(alias = "ST0CH1SET")]
pub type St0ch1set = crate::Reg<st0ch1set::St0ch1setSpec>;
#[doc = "SHRTIMER Slave_TIMER0 channel 1 set request register"]
pub mod st0ch1set;
#[doc = "ST0CH1RST (rw) register accessor: SHRTIMER Slave_TIMER0 channel 1 reset request register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0ch1rst::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0ch1rst::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0ch1rst`]
module"]
#[doc(alias = "ST0CH1RST")]
pub type St0ch1rst = crate::Reg<st0ch1rst::St0ch1rstSpec>;
#[doc = "SHRTIMER Slave_TIMER0 channel 1 reset request register"]
pub mod st0ch1rst;
#[doc = "ST0EXEVFCFG0 (rw) register accessor: SHRTIMER Slave_TIMERx external event filter configuration register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0exevfcfg0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0exevfcfg0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0exevfcfg0`]
module"]
#[doc(alias = "ST0EXEVFCFG0")]
pub type St0exevfcfg0 = crate::Reg<st0exevfcfg0::St0exevfcfg0Spec>;
#[doc = "SHRTIMER Slave_TIMERx external event filter configuration register 0"]
pub mod st0exevfcfg0;
#[doc = "ST0EXEVFCFG1 (rw) register accessor: SHRTIMER Slave_TIMERx external event filter configuration register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0exevfcfg1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0exevfcfg1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0exevfcfg1`]
module"]
#[doc(alias = "ST0EXEVFCFG1")]
pub type St0exevfcfg1 = crate::Reg<st0exevfcfg1::St0exevfcfg1Spec>;
#[doc = "SHRTIMER Slave_TIMERx external event filter configuration register 1"]
pub mod st0exevfcfg1;
#[doc = "ST0CNTRST (rw) register accessor: SHRTIMER Slave_TIMER0 counter reset register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0cntrst::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0cntrst::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0cntrst`]
module"]
#[doc(alias = "ST0CNTRST")]
pub type St0cntrst = crate::Reg<st0cntrst::St0cntrstSpec>;
#[doc = "SHRTIMER Slave_TIMER0 counter reset register"]
pub mod st0cntrst;
#[doc = "ST0CSCTL (rw) register accessor: SHRTIMER Slave_TIMERx carrier-signal control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0csctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0csctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0csctl`]
module"]
#[doc(alias = "ST0CSCTL")]
pub type St0csctl = crate::Reg<st0csctl::St0csctlSpec>;
#[doc = "SHRTIMER Slave_TIMERx carrier-signal control register"]
pub mod st0csctl;
#[doc = "ST0CAP0TRG (rw) register accessor: SHRTIMER Slave_TIMER0 capture 0 trigger register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0cap0trg::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0cap0trg::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0cap0trg`]
module"]
#[doc(alias = "ST0CAP0TRG")]
pub type St0cap0trg = crate::Reg<st0cap0trg::St0cap0trgSpec>;
#[doc = "SHRTIMER Slave_TIMER0 capture 0 trigger register"]
pub mod st0cap0trg;
#[doc = "ST0CAP1TRG (rw) register accessor: SHRTIMER Slave_TIMER0 capture 1 trigger register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0cap1trg::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0cap1trg::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0cap1trg`]
module"]
#[doc(alias = "ST0CAP1TRG")]
pub type St0cap1trg = crate::Reg<st0cap1trg::St0cap1trgSpec>;
#[doc = "SHRTIMER Slave_TIMER0 capture 1 trigger register"]
pub mod st0cap1trg;
#[doc = "ST0CHOCTL (rw) register accessor: SHRTIMER Slave_TIMERx channel output control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0choctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0choctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0choctl`]
module"]
#[doc(alias = "ST0CHOCTL")]
pub type St0choctl = crate::Reg<st0choctl::St0choctlSpec>;
#[doc = "SHRTIMER Slave_TIMERx channel output control register"]
pub mod st0choctl;
#[doc = "ST0FLTCTL (rw) register accessor: SHRTIMER Slave_TIMERx fault control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0fltctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0fltctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0fltctl`]
module"]
#[doc(alias = "ST0FLTCTL")]
pub type St0fltctl = crate::Reg<st0fltctl::St0fltctlSpec>;
#[doc = "SHRTIMER Slave_TIMERx fault control register"]
pub mod st0fltctl;
#[doc = "ST0ACTL (rw) register accessor: SHRTIMER Slave_TIMERx additional control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0actl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0actl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st0actl`]
module"]
#[doc(alias = "ST0ACTL")]
pub type St0actl = crate::Reg<st0actl::St0actlSpec>;
#[doc = "SHRTIMER Slave_TIMERx additional control register"]
pub mod st0actl;
