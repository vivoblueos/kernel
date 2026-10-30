#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    st1ctl0: St1ctl0,
    st1intf: St1intf,
    st1intc: St1intc,
    st1dmainten: St1dmainten,
    st1cnt: St1cnt,
    st1car: St1car,
    st1crep: St1crep,
    st1cmp0v: St1cmp0v,
    st1cmp0cp: St1cmp0cp,
    st1cmp1v: St1cmp1v,
    st1cmp2v: St1cmp2v,
    st1cmp3v: St1cmp3v,
    st1cap0v: St1cap0v,
    st1cap1v: St1cap1v,
    st1dtctl: St1dtctl,
    st1ch0set: St1ch0set,
    st1ch0rst: St1ch0rst,
    st1ch1set: St1ch1set,
    st1ch1rst: St1ch1rst,
    st1exevfcfg0: St1exevfcfg0,
    st1exevfcfg1: St1exevfcfg1,
    st1cntrst: St1cntrst,
    st1csctl: St1csctl,
    st1cap0trg: St1cap0trg,
    st1cap1trg: St1cap1trg,
    st1choctl: St1choctl,
    st1fltctl: St1fltctl,
    _reserved27: [u8; 0x10],
    st1actl: St1actl,
}
impl RegisterBlock {
    #[doc = "0x00 - SHRTIMER Slave_TIMER1 control register 0"]
    #[inline(always)]
    pub const fn st1ctl0(&self) -> &St1ctl0 {
        &self.st1ctl0
    }
    #[doc = "0x04 - SHRTIMER Slave_TIMER1 interrupt flag register"]
    #[inline(always)]
    pub const fn st1intf(&self) -> &St1intf {
        &self.st1intf
    }
    #[doc = "0x08 - SHRTIMER Slave_TIMER1 interrupt flag clear register"]
    #[inline(always)]
    pub const fn st1intc(&self) -> &St1intc {
        &self.st1intc
    }
    #[doc = "0x0c - SHRTIMER Slave_TIMER1 DMA and interrupt enable register"]
    #[inline(always)]
    pub const fn st1dmainten(&self) -> &St1dmainten {
        &self.st1dmainten
    }
    #[doc = "0x10 - SHRTIMER Slave_TIMER1 counter register"]
    #[inline(always)]
    pub const fn st1cnt(&self) -> &St1cnt {
        &self.st1cnt
    }
    #[doc = "0x14 - SHRTIMER Slave_TIMER1 counter auto reload register"]
    #[inline(always)]
    pub const fn st1car(&self) -> &St1car {
        &self.st1car
    }
    #[doc = "0x18 - SHRTIMER Slave_TIMER1 counter repetition register"]
    #[inline(always)]
    pub const fn st1crep(&self) -> &St1crep {
        &self.st1crep
    }
    #[doc = "0x1c - SHRTIMER Slave_TIMER1 compare 0 value register"]
    #[inline(always)]
    pub const fn st1cmp0v(&self) -> &St1cmp0v {
        &self.st1cmp0v
    }
    #[doc = "0x20 - SHRTIMER Slave_TIMER1 compare 0 composite register"]
    #[inline(always)]
    pub const fn st1cmp0cp(&self) -> &St1cmp0cp {
        &self.st1cmp0cp
    }
    #[doc = "0x24 - SHRTIMER Slave_TIMER1 compare 1 value register"]
    #[inline(always)]
    pub const fn st1cmp1v(&self) -> &St1cmp1v {
        &self.st1cmp1v
    }
    #[doc = "0x28 - SHRTIMER Slave_TIMER1 compare 2 value register"]
    #[inline(always)]
    pub const fn st1cmp2v(&self) -> &St1cmp2v {
        &self.st1cmp2v
    }
    #[doc = "0x2c - SHRTIMER Slave_TIMER1 compare 3 value register"]
    #[inline(always)]
    pub const fn st1cmp3v(&self) -> &St1cmp3v {
        &self.st1cmp3v
    }
    #[doc = "0x30 - SHRTIMER Slave_TIMER1 capture 0 value register"]
    #[inline(always)]
    pub const fn st1cap0v(&self) -> &St1cap0v {
        &self.st1cap0v
    }
    #[doc = "0x34 - SHRTIMER Slave_TIMER1 capture 1 value register"]
    #[inline(always)]
    pub const fn st1cap1v(&self) -> &St1cap1v {
        &self.st1cap1v
    }
    #[doc = "0x38 - SHRTIMER Slave_TIMER1 dead-time control register"]
    #[inline(always)]
    pub const fn st1dtctl(&self) -> &St1dtctl {
        &self.st1dtctl
    }
    #[doc = "0x3c - SHRTIMER Slave_TIMER1 channel 0 set request register"]
    #[inline(always)]
    pub const fn st1ch0set(&self) -> &St1ch0set {
        &self.st1ch0set
    }
    #[doc = "0x40 - SHRTIMER Slave_TIMER1 channel 0 reset request register"]
    #[inline(always)]
    pub const fn st1ch0rst(&self) -> &St1ch0rst {
        &self.st1ch0rst
    }
    #[doc = "0x44 - SHRTIMER Slave_TIMER1 channel 1 set request register"]
    #[inline(always)]
    pub const fn st1ch1set(&self) -> &St1ch1set {
        &self.st1ch1set
    }
    #[doc = "0x48 - SHRTIMER Slave_TIMER1 channel 1 reset request register"]
    #[inline(always)]
    pub const fn st1ch1rst(&self) -> &St1ch1rst {
        &self.st1ch1rst
    }
    #[doc = "0x4c - SHRTIMER Slave_TIMERx external event filter configuration register 0"]
    #[inline(always)]
    pub const fn st1exevfcfg0(&self) -> &St1exevfcfg0 {
        &self.st1exevfcfg0
    }
    #[doc = "0x50 - SHRTIMER Slave_TIMERx external event filter configuration register 1"]
    #[inline(always)]
    pub const fn st1exevfcfg1(&self) -> &St1exevfcfg1 {
        &self.st1exevfcfg1
    }
    #[doc = "0x54 - SHRTIMER Slave_TIMERx counter reset register"]
    #[inline(always)]
    pub const fn st1cntrst(&self) -> &St1cntrst {
        &self.st1cntrst
    }
    #[doc = "0x58 - SHRTIMER Slave_TIMERx carrier-signal control register"]
    #[inline(always)]
    pub const fn st1csctl(&self) -> &St1csctl {
        &self.st1csctl
    }
    #[doc = "0x5c - SHRTIMER Slave_TIMERx capture 0 trigger register"]
    #[inline(always)]
    pub const fn st1cap0trg(&self) -> &St1cap0trg {
        &self.st1cap0trg
    }
    #[doc = "0x60 - SHRTIMER Slave_TIMERx capture 1 trigger register"]
    #[inline(always)]
    pub const fn st1cap1trg(&self) -> &St1cap1trg {
        &self.st1cap1trg
    }
    #[doc = "0x64 - SHRTIMER Slave_TIMERx channel output control register"]
    #[inline(always)]
    pub const fn st1choctl(&self) -> &St1choctl {
        &self.st1choctl
    }
    #[doc = "0x68 - SHRTIMER Slave_TIMERx fault control register"]
    #[inline(always)]
    pub const fn st1fltctl(&self) -> &St1fltctl {
        &self.st1fltctl
    }
    #[doc = "0x7c - SHRTIMER Slave_TIMERx additional control register"]
    #[inline(always)]
    pub const fn st1actl(&self) -> &St1actl {
        &self.st1actl
    }
}
#[doc = "ST1CTL0 (rw) register accessor: SHRTIMER Slave_TIMER1 control register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1ctl0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1ctl0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1ctl0`]
module"]
#[doc(alias = "ST1CTL0")]
pub type St1ctl0 = crate::Reg<st1ctl0::St1ctl0Spec>;
#[doc = "SHRTIMER Slave_TIMER1 control register 0"]
pub mod st1ctl0;
#[doc = "ST1INTF (r) register accessor: SHRTIMER Slave_TIMER1 interrupt flag register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1intf::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1intf`]
module"]
#[doc(alias = "ST1INTF")]
pub type St1intf = crate::Reg<st1intf::St1intfSpec>;
#[doc = "SHRTIMER Slave_TIMER1 interrupt flag register"]
pub mod st1intf;
#[doc = "ST1INTC (w) register accessor: SHRTIMER Slave_TIMER1 interrupt flag clear register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1intc::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1intc`]
module"]
#[doc(alias = "ST1INTC")]
pub type St1intc = crate::Reg<st1intc::St1intcSpec>;
#[doc = "SHRTIMER Slave_TIMER1 interrupt flag clear register"]
pub mod st1intc;
#[doc = "ST1DMAINTEN (rw) register accessor: SHRTIMER Slave_TIMER1 DMA and interrupt enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1dmainten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1dmainten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1dmainten`]
module"]
#[doc(alias = "ST1DMAINTEN")]
pub type St1dmainten = crate::Reg<st1dmainten::St1dmaintenSpec>;
#[doc = "SHRTIMER Slave_TIMER1 DMA and interrupt enable register"]
pub mod st1dmainten;
#[doc = "ST1CNT (rw) register accessor: SHRTIMER Slave_TIMER1 counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1cnt::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1cnt::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1cnt`]
module"]
#[doc(alias = "ST1CNT")]
pub type St1cnt = crate::Reg<st1cnt::St1cntSpec>;
#[doc = "SHRTIMER Slave_TIMER1 counter register"]
pub mod st1cnt;
#[doc = "ST1CAR (rw) register accessor: SHRTIMER Slave_TIMER1 counter auto reload register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1car::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1car::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1car`]
module"]
#[doc(alias = "ST1CAR")]
pub type St1car = crate::Reg<st1car::St1carSpec>;
#[doc = "SHRTIMER Slave_TIMER1 counter auto reload register"]
pub mod st1car;
#[doc = "ST1CREP (rw) register accessor: SHRTIMER Slave_TIMER1 counter repetition register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1crep::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1crep::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1crep`]
module"]
#[doc(alias = "ST1CREP")]
pub type St1crep = crate::Reg<st1crep::St1crepSpec>;
#[doc = "SHRTIMER Slave_TIMER1 counter repetition register"]
pub mod st1crep;
#[doc = "ST1CMP0V (rw) register accessor: SHRTIMER Slave_TIMER1 compare 0 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1cmp0v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1cmp0v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1cmp0v`]
module"]
#[doc(alias = "ST1CMP0V")]
pub type St1cmp0v = crate::Reg<st1cmp0v::St1cmp0vSpec>;
#[doc = "SHRTIMER Slave_TIMER1 compare 0 value register"]
pub mod st1cmp0v;
#[doc = "ST1CMP0CP (rw) register accessor: SHRTIMER Slave_TIMER1 compare 0 composite register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1cmp0cp::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1cmp0cp::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1cmp0cp`]
module"]
#[doc(alias = "ST1CMP0CP")]
pub type St1cmp0cp = crate::Reg<st1cmp0cp::St1cmp0cpSpec>;
#[doc = "SHRTIMER Slave_TIMER1 compare 0 composite register"]
pub mod st1cmp0cp;
#[doc = "ST1CMP1V (rw) register accessor: SHRTIMER Slave_TIMER1 compare 1 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1cmp1v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1cmp1v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1cmp1v`]
module"]
#[doc(alias = "ST1CMP1V")]
pub type St1cmp1v = crate::Reg<st1cmp1v::St1cmp1vSpec>;
#[doc = "SHRTIMER Slave_TIMER1 compare 1 value register"]
pub mod st1cmp1v;
#[doc = "ST1CMP2V (rw) register accessor: SHRTIMER Slave_TIMER1 compare 2 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1cmp2v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1cmp2v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1cmp2v`]
module"]
#[doc(alias = "ST1CMP2V")]
pub type St1cmp2v = crate::Reg<st1cmp2v::St1cmp2vSpec>;
#[doc = "SHRTIMER Slave_TIMER1 compare 2 value register"]
pub mod st1cmp2v;
#[doc = "ST1CMP3V (rw) register accessor: SHRTIMER Slave_TIMER1 compare 3 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1cmp3v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1cmp3v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1cmp3v`]
module"]
#[doc(alias = "ST1CMP3V")]
pub type St1cmp3v = crate::Reg<st1cmp3v::St1cmp3vSpec>;
#[doc = "SHRTIMER Slave_TIMER1 compare 3 value register"]
pub mod st1cmp3v;
#[doc = "ST1CAP0V (rw) register accessor: SHRTIMER Slave_TIMER1 capture 0 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1cap0v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1cap0v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1cap0v`]
module"]
#[doc(alias = "ST1CAP0V")]
pub type St1cap0v = crate::Reg<st1cap0v::St1cap0vSpec>;
#[doc = "SHRTIMER Slave_TIMER1 capture 0 value register"]
pub mod st1cap0v;
#[doc = "ST1CAP1V (rw) register accessor: SHRTIMER Slave_TIMER1 capture 1 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1cap1v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1cap1v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1cap1v`]
module"]
#[doc(alias = "ST1CAP1V")]
pub type St1cap1v = crate::Reg<st1cap1v::St1cap1vSpec>;
#[doc = "SHRTIMER Slave_TIMER1 capture 1 value register"]
pub mod st1cap1v;
#[doc = "ST1DTCTL (rw) register accessor: SHRTIMER Slave_TIMER1 dead-time control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1dtctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1dtctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1dtctl`]
module"]
#[doc(alias = "ST1DTCTL")]
pub type St1dtctl = crate::Reg<st1dtctl::St1dtctlSpec>;
#[doc = "SHRTIMER Slave_TIMER1 dead-time control register"]
pub mod st1dtctl;
#[doc = "ST1CH0SET (rw) register accessor: SHRTIMER Slave_TIMER1 channel 0 set request register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1ch0set::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1ch0set::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1ch0set`]
module"]
#[doc(alias = "ST1CH0SET")]
pub type St1ch0set = crate::Reg<st1ch0set::St1ch0setSpec>;
#[doc = "SHRTIMER Slave_TIMER1 channel 0 set request register"]
pub mod st1ch0set;
#[doc = "ST1CH0RST (rw) register accessor: SHRTIMER Slave_TIMER1 channel 0 reset request register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1ch0rst::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1ch0rst::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1ch0rst`]
module"]
#[doc(alias = "ST1CH0RST")]
pub type St1ch0rst = crate::Reg<st1ch0rst::St1ch0rstSpec>;
#[doc = "SHRTIMER Slave_TIMER1 channel 0 reset request register"]
pub mod st1ch0rst;
#[doc = "ST1CH1SET (rw) register accessor: SHRTIMER Slave_TIMER1 channel 1 set request register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1ch1set::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1ch1set::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1ch1set`]
module"]
#[doc(alias = "ST1CH1SET")]
pub type St1ch1set = crate::Reg<st1ch1set::St1ch1setSpec>;
#[doc = "SHRTIMER Slave_TIMER1 channel 1 set request register"]
pub mod st1ch1set;
#[doc = "ST1CH1RST (rw) register accessor: SHRTIMER Slave_TIMER1 channel 1 reset request register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1ch1rst::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1ch1rst::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1ch1rst`]
module"]
#[doc(alias = "ST1CH1RST")]
pub type St1ch1rst = crate::Reg<st1ch1rst::St1ch1rstSpec>;
#[doc = "SHRTIMER Slave_TIMER1 channel 1 reset request register"]
pub mod st1ch1rst;
#[doc = "ST1EXEVFCFG0 (rw) register accessor: SHRTIMER Slave_TIMERx external event filter configuration register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1exevfcfg0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1exevfcfg0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1exevfcfg0`]
module"]
#[doc(alias = "ST1EXEVFCFG0")]
pub type St1exevfcfg0 = crate::Reg<st1exevfcfg0::St1exevfcfg0Spec>;
#[doc = "SHRTIMER Slave_TIMERx external event filter configuration register 0"]
pub mod st1exevfcfg0;
#[doc = "ST1EXEVFCFG1 (rw) register accessor: SHRTIMER Slave_TIMERx external event filter configuration register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1exevfcfg1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1exevfcfg1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1exevfcfg1`]
module"]
#[doc(alias = "ST1EXEVFCFG1")]
pub type St1exevfcfg1 = crate::Reg<st1exevfcfg1::St1exevfcfg1Spec>;
#[doc = "SHRTIMER Slave_TIMERx external event filter configuration register 1"]
pub mod st1exevfcfg1;
#[doc = "ST1CNTRST (rw) register accessor: SHRTIMER Slave_TIMERx counter reset register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1cntrst::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1cntrst::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1cntrst`]
module"]
#[doc(alias = "ST1CNTRST")]
pub type St1cntrst = crate::Reg<st1cntrst::St1cntrstSpec>;
#[doc = "SHRTIMER Slave_TIMERx counter reset register"]
pub mod st1cntrst;
#[doc = "ST1CSCTL (rw) register accessor: SHRTIMER Slave_TIMERx carrier-signal control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1csctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1csctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1csctl`]
module"]
#[doc(alias = "ST1CSCTL")]
pub type St1csctl = crate::Reg<st1csctl::St1csctlSpec>;
#[doc = "SHRTIMER Slave_TIMERx carrier-signal control register"]
pub mod st1csctl;
#[doc = "ST1CAP0TRG (rw) register accessor: SHRTIMER Slave_TIMERx capture 0 trigger register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1cap0trg::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1cap0trg::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1cap0trg`]
module"]
#[doc(alias = "ST1CAP0TRG")]
pub type St1cap0trg = crate::Reg<st1cap0trg::St1cap0trgSpec>;
#[doc = "SHRTIMER Slave_TIMERx capture 0 trigger register"]
pub mod st1cap0trg;
#[doc = "ST1CAP1TRG (rw) register accessor: SHRTIMER Slave_TIMERx capture 1 trigger register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1cap1trg::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1cap1trg::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1cap1trg`]
module"]
#[doc(alias = "ST1CAP1TRG")]
pub type St1cap1trg = crate::Reg<st1cap1trg::St1cap1trgSpec>;
#[doc = "SHRTIMER Slave_TIMERx capture 1 trigger register"]
pub mod st1cap1trg;
#[doc = "ST1CHOCTL (rw) register accessor: SHRTIMER Slave_TIMERx channel output control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1choctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1choctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1choctl`]
module"]
#[doc(alias = "ST1CHOCTL")]
pub type St1choctl = crate::Reg<st1choctl::St1choctlSpec>;
#[doc = "SHRTIMER Slave_TIMERx channel output control register"]
pub mod st1choctl;
#[doc = "ST1FLTCTL (rw) register accessor: SHRTIMER Slave_TIMERx fault control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1fltctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1fltctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1fltctl`]
module"]
#[doc(alias = "ST1FLTCTL")]
pub type St1fltctl = crate::Reg<st1fltctl::St1fltctlSpec>;
#[doc = "SHRTIMER Slave_TIMERx fault control register"]
pub mod st1fltctl;
#[doc = "ST1ACTL (rw) register accessor: SHRTIMER Slave_TIMERx additional control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st1actl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st1actl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st1actl`]
module"]
#[doc(alias = "ST1ACTL")]
pub type St1actl = crate::Reg<st1actl::St1actlSpec>;
#[doc = "SHRTIMER Slave_TIMERx additional control register"]
pub mod st1actl;
