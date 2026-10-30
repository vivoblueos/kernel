#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    st2ctl0: St2ctl0,
    st2intf: St2intf,
    st2intc: St2intc,
    st2dmainten: St2dmainten,
    st2cnt: St2cnt,
    st2car: St2car,
    st2crep: St2crep,
    st2cmp0v: St2cmp0v,
    st2cmp0cp: St2cmp0cp,
    st2cmp1v: St2cmp1v,
    st2cmp2v: St2cmp2v,
    st2cmp3v: St2cmp3v,
    st2cap0v: St2cap0v,
    st2cap1v: St2cap1v,
    st2dtctl: St2dtctl,
    st2ch0set: St2ch0set,
    st2ch0rst: St2ch0rst,
    st2ch1set: St2ch1set,
    st2ch1rst: St2ch1rst,
    st2exevfcfg0: St2exevfcfg0,
    st2exevfcfg1: St2exevfcfg1,
    st2cntrst: St2cntrst,
    st2csctl: St2csctl,
    st2cap0trg: St2cap0trg,
    st2cap1trg: St2cap1trg,
    st2choctl: St2choctl,
    st2fltctl: St2fltctl,
    _reserved27: [u8; 0x10],
    st2actl: St2actl,
}
impl RegisterBlock {
    #[doc = "0x00 - SHRTIMER Slave_TIMERx control register 0"]
    #[inline(always)]
    pub const fn st2ctl0(&self) -> &St2ctl0 {
        &self.st2ctl0
    }
    #[doc = "0x04 - SHRTIMER Slave_TIMERx interrupt flag register"]
    #[inline(always)]
    pub const fn st2intf(&self) -> &St2intf {
        &self.st2intf
    }
    #[doc = "0x08 - SHRTIMER Slave_TIMERx interrupt flag clear register"]
    #[inline(always)]
    pub const fn st2intc(&self) -> &St2intc {
        &self.st2intc
    }
    #[doc = "0x0c - SHRTIMER Slave_TIMERx DMA and interrupt enable register"]
    #[inline(always)]
    pub const fn st2dmainten(&self) -> &St2dmainten {
        &self.st2dmainten
    }
    #[doc = "0x10 - SHRTIMER Slave_TIMERx counter register"]
    #[inline(always)]
    pub const fn st2cnt(&self) -> &St2cnt {
        &self.st2cnt
    }
    #[doc = "0x14 - SHRTIMER Slave_TIMER2 counter auto reload register"]
    #[inline(always)]
    pub const fn st2car(&self) -> &St2car {
        &self.st2car
    }
    #[doc = "0x18 - SHRTIMER Slave_TIMER2 counter repetition register"]
    #[inline(always)]
    pub const fn st2crep(&self) -> &St2crep {
        &self.st2crep
    }
    #[doc = "0x1c - SHRTIMER Slave_TIMER2 compare 0 value register"]
    #[inline(always)]
    pub const fn st2cmp0v(&self) -> &St2cmp0v {
        &self.st2cmp0v
    }
    #[doc = "0x20 - SHRTIMER Slave_TIMERx compare 0 composite register"]
    #[inline(always)]
    pub const fn st2cmp0cp(&self) -> &St2cmp0cp {
        &self.st2cmp0cp
    }
    #[doc = "0x24 - SHRTIMER Slave_TIMERx compare 1 value register"]
    #[inline(always)]
    pub const fn st2cmp1v(&self) -> &St2cmp1v {
        &self.st2cmp1v
    }
    #[doc = "0x28 - SHRTIMER Slave_TIMERx compare 2 value register"]
    #[inline(always)]
    pub const fn st2cmp2v(&self) -> &St2cmp2v {
        &self.st2cmp2v
    }
    #[doc = "0x2c - SHRTIMER Slave_TIMERx compare 3 value register"]
    #[inline(always)]
    pub const fn st2cmp3v(&self) -> &St2cmp3v {
        &self.st2cmp3v
    }
    #[doc = "0x30 - SHRTIMER Slave_TIMERx capture 0 value register"]
    #[inline(always)]
    pub const fn st2cap0v(&self) -> &St2cap0v {
        &self.st2cap0v
    }
    #[doc = "0x34 - SHRTIMER Slave_TIMERx capture 1 value register"]
    #[inline(always)]
    pub const fn st2cap1v(&self) -> &St2cap1v {
        &self.st2cap1v
    }
    #[doc = "0x38 - SHRTIMER Slave_TIMERx dead-time control register"]
    #[inline(always)]
    pub const fn st2dtctl(&self) -> &St2dtctl {
        &self.st2dtctl
    }
    #[doc = "0x3c - SHRTIMER Slave_TIMERx channel 0 set request register"]
    #[inline(always)]
    pub const fn st2ch0set(&self) -> &St2ch0set {
        &self.st2ch0set
    }
    #[doc = "0x40 - SHRTIMER Slave_TIMERx channel 0 reset request register"]
    #[inline(always)]
    pub const fn st2ch0rst(&self) -> &St2ch0rst {
        &self.st2ch0rst
    }
    #[doc = "0x44 - SHRTIMER Slave_TIMERx channel 1 set request register"]
    #[inline(always)]
    pub const fn st2ch1set(&self) -> &St2ch1set {
        &self.st2ch1set
    }
    #[doc = "0x48 - SHRTIMER Slave_TIMERx channel 1 reset request register"]
    #[inline(always)]
    pub const fn st2ch1rst(&self) -> &St2ch1rst {
        &self.st2ch1rst
    }
    #[doc = "0x4c - SHRTIMER Slave_TIMERx external event filter configuration register 0"]
    #[inline(always)]
    pub const fn st2exevfcfg0(&self) -> &St2exevfcfg0 {
        &self.st2exevfcfg0
    }
    #[doc = "0x50 - SHRTIMER Slave_TIMERx external event filter configuration register 1"]
    #[inline(always)]
    pub const fn st2exevfcfg1(&self) -> &St2exevfcfg1 {
        &self.st2exevfcfg1
    }
    #[doc = "0x54 - SHRTIMER Slave_TIMERx counter reset register"]
    #[inline(always)]
    pub const fn st2cntrst(&self) -> &St2cntrst {
        &self.st2cntrst
    }
    #[doc = "0x58 - SHRTIMER Slave_TIMERx carrier-signal control register"]
    #[inline(always)]
    pub const fn st2csctl(&self) -> &St2csctl {
        &self.st2csctl
    }
    #[doc = "0x5c - SHRTIMER Slave_TIMERx capture 0 trigger register"]
    #[inline(always)]
    pub const fn st2cap0trg(&self) -> &St2cap0trg {
        &self.st2cap0trg
    }
    #[doc = "0x60 - SHRTIMER Slave_TIMERx capture 1 trigger register"]
    #[inline(always)]
    pub const fn st2cap1trg(&self) -> &St2cap1trg {
        &self.st2cap1trg
    }
    #[doc = "0x64 - SHRTIMER Slave_TIMERx channel output control register"]
    #[inline(always)]
    pub const fn st2choctl(&self) -> &St2choctl {
        &self.st2choctl
    }
    #[doc = "0x68 - SHRTIMER Slave_TIMERx fault control register"]
    #[inline(always)]
    pub const fn st2fltctl(&self) -> &St2fltctl {
        &self.st2fltctl
    }
    #[doc = "0x7c - SHRTIMER Slave_TIMERx additional control register"]
    #[inline(always)]
    pub const fn st2actl(&self) -> &St2actl {
        &self.st2actl
    }
}
#[doc = "ST2CTL0 (rw) register accessor: SHRTIMER Slave_TIMERx control register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2ctl0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2ctl0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2ctl0`]
module"]
#[doc(alias = "ST2CTL0")]
pub type St2ctl0 = crate::Reg<st2ctl0::St2ctl0Spec>;
#[doc = "SHRTIMER Slave_TIMERx control register 0"]
pub mod st2ctl0;
#[doc = "ST2INTF (r) register accessor: SHRTIMER Slave_TIMERx interrupt flag register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2intf::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2intf`]
module"]
#[doc(alias = "ST2INTF")]
pub type St2intf = crate::Reg<st2intf::St2intfSpec>;
#[doc = "SHRTIMER Slave_TIMERx interrupt flag register"]
pub mod st2intf;
#[doc = "ST2INTC (w) register accessor: SHRTIMER Slave_TIMERx interrupt flag clear register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2intc::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2intc`]
module"]
#[doc(alias = "ST2INTC")]
pub type St2intc = crate::Reg<st2intc::St2intcSpec>;
#[doc = "SHRTIMER Slave_TIMERx interrupt flag clear register"]
pub mod st2intc;
#[doc = "ST2DMAINTEN (rw) register accessor: SHRTIMER Slave_TIMERx DMA and interrupt enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2dmainten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2dmainten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2dmainten`]
module"]
#[doc(alias = "ST2DMAINTEN")]
pub type St2dmainten = crate::Reg<st2dmainten::St2dmaintenSpec>;
#[doc = "SHRTIMER Slave_TIMERx DMA and interrupt enable register"]
pub mod st2dmainten;
#[doc = "ST2CNT (rw) register accessor: SHRTIMER Slave_TIMERx counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2cnt::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2cnt::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2cnt`]
module"]
#[doc(alias = "ST2CNT")]
pub type St2cnt = crate::Reg<st2cnt::St2cntSpec>;
#[doc = "SHRTIMER Slave_TIMERx counter register"]
pub mod st2cnt;
#[doc = "ST2CAR (rw) register accessor: SHRTIMER Slave_TIMER2 counter auto reload register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2car::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2car::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2car`]
module"]
#[doc(alias = "ST2CAR")]
pub type St2car = crate::Reg<st2car::St2carSpec>;
#[doc = "SHRTIMER Slave_TIMER2 counter auto reload register"]
pub mod st2car;
#[doc = "ST2CREP (rw) register accessor: SHRTIMER Slave_TIMER2 counter repetition register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2crep::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2crep::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2crep`]
module"]
#[doc(alias = "ST2CREP")]
pub type St2crep = crate::Reg<st2crep::St2crepSpec>;
#[doc = "SHRTIMER Slave_TIMER2 counter repetition register"]
pub mod st2crep;
#[doc = "ST2CMP0V (rw) register accessor: SHRTIMER Slave_TIMER2 compare 0 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2cmp0v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2cmp0v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2cmp0v`]
module"]
#[doc(alias = "ST2CMP0V")]
pub type St2cmp0v = crate::Reg<st2cmp0v::St2cmp0vSpec>;
#[doc = "SHRTIMER Slave_TIMER2 compare 0 value register"]
pub mod st2cmp0v;
#[doc = "ST2CMP0CP (rw) register accessor: SHRTIMER Slave_TIMERx compare 0 composite register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2cmp0cp::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2cmp0cp::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2cmp0cp`]
module"]
#[doc(alias = "ST2CMP0CP")]
pub type St2cmp0cp = crate::Reg<st2cmp0cp::St2cmp0cpSpec>;
#[doc = "SHRTIMER Slave_TIMERx compare 0 composite register"]
pub mod st2cmp0cp;
#[doc = "ST2CMP1V (rw) register accessor: SHRTIMER Slave_TIMERx compare 1 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2cmp1v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2cmp1v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2cmp1v`]
module"]
#[doc(alias = "ST2CMP1V")]
pub type St2cmp1v = crate::Reg<st2cmp1v::St2cmp1vSpec>;
#[doc = "SHRTIMER Slave_TIMERx compare 1 value register"]
pub mod st2cmp1v;
#[doc = "ST2CMP2V (rw) register accessor: SHRTIMER Slave_TIMERx compare 2 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2cmp2v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2cmp2v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2cmp2v`]
module"]
#[doc(alias = "ST2CMP2V")]
pub type St2cmp2v = crate::Reg<st2cmp2v::St2cmp2vSpec>;
#[doc = "SHRTIMER Slave_TIMERx compare 2 value register"]
pub mod st2cmp2v;
#[doc = "ST2CMP3V (rw) register accessor: SHRTIMER Slave_TIMERx compare 3 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2cmp3v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2cmp3v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2cmp3v`]
module"]
#[doc(alias = "ST2CMP3V")]
pub type St2cmp3v = crate::Reg<st2cmp3v::St2cmp3vSpec>;
#[doc = "SHRTIMER Slave_TIMERx compare 3 value register"]
pub mod st2cmp3v;
#[doc = "ST2CAP0V (rw) register accessor: SHRTIMER Slave_TIMERx capture 0 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2cap0v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2cap0v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2cap0v`]
module"]
#[doc(alias = "ST2CAP0V")]
pub type St2cap0v = crate::Reg<st2cap0v::St2cap0vSpec>;
#[doc = "SHRTIMER Slave_TIMERx capture 0 value register"]
pub mod st2cap0v;
#[doc = "ST2CAP1V (rw) register accessor: SHRTIMER Slave_TIMERx capture 1 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2cap1v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2cap1v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2cap1v`]
module"]
#[doc(alias = "ST2CAP1V")]
pub type St2cap1v = crate::Reg<st2cap1v::St2cap1vSpec>;
#[doc = "SHRTIMER Slave_TIMERx capture 1 value register"]
pub mod st2cap1v;
#[doc = "ST2DTCTL (rw) register accessor: SHRTIMER Slave_TIMERx dead-time control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2dtctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2dtctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2dtctl`]
module"]
#[doc(alias = "ST2DTCTL")]
pub type St2dtctl = crate::Reg<st2dtctl::St2dtctlSpec>;
#[doc = "SHRTIMER Slave_TIMERx dead-time control register"]
pub mod st2dtctl;
#[doc = "ST2CH0SET (rw) register accessor: SHRTIMER Slave_TIMERx channel 0 set request register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2ch0set::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2ch0set::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2ch0set`]
module"]
#[doc(alias = "ST2CH0SET")]
pub type St2ch0set = crate::Reg<st2ch0set::St2ch0setSpec>;
#[doc = "SHRTIMER Slave_TIMERx channel 0 set request register"]
pub mod st2ch0set;
#[doc = "ST2CH0RST (rw) register accessor: SHRTIMER Slave_TIMERx channel 0 reset request register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2ch0rst::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2ch0rst::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2ch0rst`]
module"]
#[doc(alias = "ST2CH0RST")]
pub type St2ch0rst = crate::Reg<st2ch0rst::St2ch0rstSpec>;
#[doc = "SHRTIMER Slave_TIMERx channel 0 reset request register"]
pub mod st2ch0rst;
#[doc = "ST2CH1SET (rw) register accessor: SHRTIMER Slave_TIMERx channel 1 set request register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2ch1set::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2ch1set::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2ch1set`]
module"]
#[doc(alias = "ST2CH1SET")]
pub type St2ch1set = crate::Reg<st2ch1set::St2ch1setSpec>;
#[doc = "SHRTIMER Slave_TIMERx channel 1 set request register"]
pub mod st2ch1set;
#[doc = "ST2CH1RST (rw) register accessor: SHRTIMER Slave_TIMERx channel 1 reset request register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2ch1rst::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2ch1rst::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2ch1rst`]
module"]
#[doc(alias = "ST2CH1RST")]
pub type St2ch1rst = crate::Reg<st2ch1rst::St2ch1rstSpec>;
#[doc = "SHRTIMER Slave_TIMERx channel 1 reset request register"]
pub mod st2ch1rst;
#[doc = "ST2EXEVFCFG0 (rw) register accessor: SHRTIMER Slave_TIMERx external event filter configuration register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2exevfcfg0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2exevfcfg0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2exevfcfg0`]
module"]
#[doc(alias = "ST2EXEVFCFG0")]
pub type St2exevfcfg0 = crate::Reg<st2exevfcfg0::St2exevfcfg0Spec>;
#[doc = "SHRTIMER Slave_TIMERx external event filter configuration register 0"]
pub mod st2exevfcfg0;
#[doc = "ST2EXEVFCFG1 (rw) register accessor: SHRTIMER Slave_TIMERx external event filter configuration register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2exevfcfg1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2exevfcfg1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2exevfcfg1`]
module"]
#[doc(alias = "ST2EXEVFCFG1")]
pub type St2exevfcfg1 = crate::Reg<st2exevfcfg1::St2exevfcfg1Spec>;
#[doc = "SHRTIMER Slave_TIMERx external event filter configuration register 1"]
pub mod st2exevfcfg1;
#[doc = "ST2CNTRST (rw) register accessor: SHRTIMER Slave_TIMERx counter reset register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2cntrst::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2cntrst::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2cntrst`]
module"]
#[doc(alias = "ST2CNTRST")]
pub type St2cntrst = crate::Reg<st2cntrst::St2cntrstSpec>;
#[doc = "SHRTIMER Slave_TIMERx counter reset register"]
pub mod st2cntrst;
#[doc = "ST2CSCTL (rw) register accessor: SHRTIMER Slave_TIMERx carrier-signal control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2csctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2csctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2csctl`]
module"]
#[doc(alias = "ST2CSCTL")]
pub type St2csctl = crate::Reg<st2csctl::St2csctlSpec>;
#[doc = "SHRTIMER Slave_TIMERx carrier-signal control register"]
pub mod st2csctl;
#[doc = "ST2CAP0TRG (rw) register accessor: SHRTIMER Slave_TIMERx capture 0 trigger register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2cap0trg::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2cap0trg::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2cap0trg`]
module"]
#[doc(alias = "ST2CAP0TRG")]
pub type St2cap0trg = crate::Reg<st2cap0trg::St2cap0trgSpec>;
#[doc = "SHRTIMER Slave_TIMERx capture 0 trigger register"]
pub mod st2cap0trg;
#[doc = "ST2CAP1TRG (rw) register accessor: SHRTIMER Slave_TIMERx capture 1 trigger register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2cap1trg::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2cap1trg::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2cap1trg`]
module"]
#[doc(alias = "ST2CAP1TRG")]
pub type St2cap1trg = crate::Reg<st2cap1trg::St2cap1trgSpec>;
#[doc = "SHRTIMER Slave_TIMERx capture 1 trigger register"]
pub mod st2cap1trg;
#[doc = "ST2CHOCTL (rw) register accessor: SHRTIMER Slave_TIMERx channel output control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2choctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2choctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2choctl`]
module"]
#[doc(alias = "ST2CHOCTL")]
pub type St2choctl = crate::Reg<st2choctl::St2choctlSpec>;
#[doc = "SHRTIMER Slave_TIMERx channel output control register"]
pub mod st2choctl;
#[doc = "ST2FLTCTL (rw) register accessor: SHRTIMER Slave_TIMERx fault control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2fltctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2fltctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2fltctl`]
module"]
#[doc(alias = "ST2FLTCTL")]
pub type St2fltctl = crate::Reg<st2fltctl::St2fltctlSpec>;
#[doc = "SHRTIMER Slave_TIMERx fault control register"]
pub mod st2fltctl;
#[doc = "ST2ACTL (rw) register accessor: SHRTIMER Slave_TIMERx additional control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st2actl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st2actl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st2actl`]
module"]
#[doc(alias = "ST2ACTL")]
pub type St2actl = crate::Reg<st2actl::St2actlSpec>;
#[doc = "SHRTIMER Slave_TIMERx additional control register"]
pub mod st2actl;
