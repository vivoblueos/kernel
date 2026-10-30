#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    st3ctl0: St3ctl0,
    st4intf: St4intf,
    st4intc: St4intc,
    st4dmainten: St4dmainten,
    st4cnt: St4cnt,
    st4car: St4car,
    st4crep: St4crep,
    st4cmp0v: St4cmp0v,
    st4cmp0cp: St4cmp0cp,
    st4cmp1v: St4cmp1v,
    st4cmp2v: St4cmp2v,
    st4cmp3v: St4cmp3v,
    st4cap0v: St4cap0v,
    st4cap1v: St4cap1v,
    st4dtctl: St4dtctl,
    st4ch0set: St4ch0set,
    st4ch0rst: St4ch0rst,
    st4ch1set: St4ch1set,
    st4ch1rst: St4ch1rst,
    st4exevfcfg0: St4exevfcfg0,
    st4exevfcfg1: St4exevfcfg1,
    st4cntrst: St4cntrst,
    st4csctl: St4csctl,
    st4cap0trg: St4cap0trg,
    st4cap1trg: St4cap1trg,
    st4choctl: St4choctl,
    st4fltctl: St4fltctl,
    _reserved27: [u8; 0x10],
    st4actl: St4actl,
}
impl RegisterBlock {
    #[doc = "0x00 - SHRTIMER Slave_TIMERx control register 0"]
    #[inline(always)]
    pub const fn st3ctl0(&self) -> &St3ctl0 {
        &self.st3ctl0
    }
    #[doc = "0x04 - SHRTIMER Slave_TIMERx interrupt flag register"]
    #[inline(always)]
    pub const fn st4intf(&self) -> &St4intf {
        &self.st4intf
    }
    #[doc = "0x08 - SHRTIMER Slave_TIMERx interrupt flag clear register"]
    #[inline(always)]
    pub const fn st4intc(&self) -> &St4intc {
        &self.st4intc
    }
    #[doc = "0x0c - SHRTIMER Slave_TIMERx DMA and interrupt enable register"]
    #[inline(always)]
    pub const fn st4dmainten(&self) -> &St4dmainten {
        &self.st4dmainten
    }
    #[doc = "0x10 - SHRTIMER Slave_TIMERx counter register"]
    #[inline(always)]
    pub const fn st4cnt(&self) -> &St4cnt {
        &self.st4cnt
    }
    #[doc = "0x14 - SHRTIMER Slave_TIMER4 counter auto reload register"]
    #[inline(always)]
    pub const fn st4car(&self) -> &St4car {
        &self.st4car
    }
    #[doc = "0x18 - SHRTIMER Slave_TIMER4 counter repetition register"]
    #[inline(always)]
    pub const fn st4crep(&self) -> &St4crep {
        &self.st4crep
    }
    #[doc = "0x1c - SHRTIMER Slave_TIMER4 compare 0 value register"]
    #[inline(always)]
    pub const fn st4cmp0v(&self) -> &St4cmp0v {
        &self.st4cmp0v
    }
    #[doc = "0x20 - SHRTIMER Slave_TIMERx compare 0 composite register"]
    #[inline(always)]
    pub const fn st4cmp0cp(&self) -> &St4cmp0cp {
        &self.st4cmp0cp
    }
    #[doc = "0x24 - SHRTIMER Slave_TIMERx compare 1 value register"]
    #[inline(always)]
    pub const fn st4cmp1v(&self) -> &St4cmp1v {
        &self.st4cmp1v
    }
    #[doc = "0x28 - SHRTIMER Slave_TIMERx compare 2 value register"]
    #[inline(always)]
    pub const fn st4cmp2v(&self) -> &St4cmp2v {
        &self.st4cmp2v
    }
    #[doc = "0x2c - SHRTIMER Slave_TIMERx compare 3 value register"]
    #[inline(always)]
    pub const fn st4cmp3v(&self) -> &St4cmp3v {
        &self.st4cmp3v
    }
    #[doc = "0x30 - SHRTIMER Slave_TIMERx capture 0 value register"]
    #[inline(always)]
    pub const fn st4cap0v(&self) -> &St4cap0v {
        &self.st4cap0v
    }
    #[doc = "0x34 - SHRTIMER Slave_TIMERx capture 1 value register"]
    #[inline(always)]
    pub const fn st4cap1v(&self) -> &St4cap1v {
        &self.st4cap1v
    }
    #[doc = "0x38 - SHRTIMER Slave_TIMERx dead-time control register"]
    #[inline(always)]
    pub const fn st4dtctl(&self) -> &St4dtctl {
        &self.st4dtctl
    }
    #[doc = "0x3c - SHRTIMER Slave_TIMERx channel 0 set request register"]
    #[inline(always)]
    pub const fn st4ch0set(&self) -> &St4ch0set {
        &self.st4ch0set
    }
    #[doc = "0x40 - SHRTIMER Slave_TIMERx channel 0 reset request register"]
    #[inline(always)]
    pub const fn st4ch0rst(&self) -> &St4ch0rst {
        &self.st4ch0rst
    }
    #[doc = "0x44 - SHRTIMER Slave_TIMERx channel 1 set request register"]
    #[inline(always)]
    pub const fn st4ch1set(&self) -> &St4ch1set {
        &self.st4ch1set
    }
    #[doc = "0x48 - SHRTIMER Slave_TIMERx channel 1 reset request register"]
    #[inline(always)]
    pub const fn st4ch1rst(&self) -> &St4ch1rst {
        &self.st4ch1rst
    }
    #[doc = "0x4c - SHRTIMER Slave_TIMERx external event filter configuration register 0"]
    #[inline(always)]
    pub const fn st4exevfcfg0(&self) -> &St4exevfcfg0 {
        &self.st4exevfcfg0
    }
    #[doc = "0x50 - SHRTIMER Slave_TIMERx external event filter configuration register 1"]
    #[inline(always)]
    pub const fn st4exevfcfg1(&self) -> &St4exevfcfg1 {
        &self.st4exevfcfg1
    }
    #[doc = "0x54 - SHRTIMER Slave_TIMERx counter reset register"]
    #[inline(always)]
    pub const fn st4cntrst(&self) -> &St4cntrst {
        &self.st4cntrst
    }
    #[doc = "0x58 - SHRTIMER Slave_TIMERx carrier-signal control register"]
    #[inline(always)]
    pub const fn st4csctl(&self) -> &St4csctl {
        &self.st4csctl
    }
    #[doc = "0x5c - SHRTIMER Slave_TIMERx capture 0 trigger register"]
    #[inline(always)]
    pub const fn st4cap0trg(&self) -> &St4cap0trg {
        &self.st4cap0trg
    }
    #[doc = "0x60 - SHRTIMER Slave_TIMERx capture 1 trigger register"]
    #[inline(always)]
    pub const fn st4cap1trg(&self) -> &St4cap1trg {
        &self.st4cap1trg
    }
    #[doc = "0x64 - SHRTIMER Slave_TIMERx channel output control register"]
    #[inline(always)]
    pub const fn st4choctl(&self) -> &St4choctl {
        &self.st4choctl
    }
    #[doc = "0x68 - SHRTIMER Slave_TIMERx fault control register"]
    #[inline(always)]
    pub const fn st4fltctl(&self) -> &St4fltctl {
        &self.st4fltctl
    }
    #[doc = "0x7c - SHRTIMER Slave_TIMERx additional control register"]
    #[inline(always)]
    pub const fn st4actl(&self) -> &St4actl {
        &self.st4actl
    }
}
#[doc = "ST3CTL0 (rw) register accessor: SHRTIMER Slave_TIMERx control register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3ctl0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3ctl0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3ctl0`]
module"]
#[doc(alias = "ST3CTL0")]
pub type St3ctl0 = crate::Reg<st3ctl0::St3ctl0Spec>;
#[doc = "SHRTIMER Slave_TIMERx control register 0"]
pub mod st3ctl0;
#[doc = "ST4INTF (r) register accessor: SHRTIMER Slave_TIMERx interrupt flag register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4intf::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4intf`]
module"]
#[doc(alias = "ST4INTF")]
pub type St4intf = crate::Reg<st4intf::St4intfSpec>;
#[doc = "SHRTIMER Slave_TIMERx interrupt flag register"]
pub mod st4intf;
#[doc = "ST4INTC (w) register accessor: SHRTIMER Slave_TIMERx interrupt flag clear register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4intc::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4intc`]
module"]
#[doc(alias = "ST4INTC")]
pub type St4intc = crate::Reg<st4intc::St4intcSpec>;
#[doc = "SHRTIMER Slave_TIMERx interrupt flag clear register"]
pub mod st4intc;
#[doc = "ST4DMAINTEN (rw) register accessor: SHRTIMER Slave_TIMERx DMA and interrupt enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4dmainten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4dmainten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4dmainten`]
module"]
#[doc(alias = "ST4DMAINTEN")]
pub type St4dmainten = crate::Reg<st4dmainten::St4dmaintenSpec>;
#[doc = "SHRTIMER Slave_TIMERx DMA and interrupt enable register"]
pub mod st4dmainten;
#[doc = "ST4CNT (rw) register accessor: SHRTIMER Slave_TIMERx counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4cnt::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4cnt::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4cnt`]
module"]
#[doc(alias = "ST4CNT")]
pub type St4cnt = crate::Reg<st4cnt::St4cntSpec>;
#[doc = "SHRTIMER Slave_TIMERx counter register"]
pub mod st4cnt;
#[doc = "ST4CAR (rw) register accessor: SHRTIMER Slave_TIMER4 counter auto reload register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4car::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4car::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4car`]
module"]
#[doc(alias = "ST4CAR")]
pub type St4car = crate::Reg<st4car::St4carSpec>;
#[doc = "SHRTIMER Slave_TIMER4 counter auto reload register"]
pub mod st4car;
#[doc = "ST4CREP (rw) register accessor: SHRTIMER Slave_TIMER4 counter repetition register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4crep::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4crep::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4crep`]
module"]
#[doc(alias = "ST4CREP")]
pub type St4crep = crate::Reg<st4crep::St4crepSpec>;
#[doc = "SHRTIMER Slave_TIMER4 counter repetition register"]
pub mod st4crep;
#[doc = "ST4CMP0V (rw) register accessor: SHRTIMER Slave_TIMER4 compare 0 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4cmp0v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4cmp0v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4cmp0v`]
module"]
#[doc(alias = "ST4CMP0V")]
pub type St4cmp0v = crate::Reg<st4cmp0v::St4cmp0vSpec>;
#[doc = "SHRTIMER Slave_TIMER4 compare 0 value register"]
pub mod st4cmp0v;
#[doc = "ST4CMP0CP (rw) register accessor: SHRTIMER Slave_TIMERx compare 0 composite register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4cmp0cp::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4cmp0cp::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4cmp0cp`]
module"]
#[doc(alias = "ST4CMP0CP")]
pub type St4cmp0cp = crate::Reg<st4cmp0cp::St4cmp0cpSpec>;
#[doc = "SHRTIMER Slave_TIMERx compare 0 composite register"]
pub mod st4cmp0cp;
#[doc = "ST4CMP1V (rw) register accessor: SHRTIMER Slave_TIMERx compare 1 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4cmp1v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4cmp1v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4cmp1v`]
module"]
#[doc(alias = "ST4CMP1V")]
pub type St4cmp1v = crate::Reg<st4cmp1v::St4cmp1vSpec>;
#[doc = "SHRTIMER Slave_TIMERx compare 1 value register"]
pub mod st4cmp1v;
#[doc = "ST4CMP2V (rw) register accessor: SHRTIMER Slave_TIMERx compare 2 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4cmp2v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4cmp2v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4cmp2v`]
module"]
#[doc(alias = "ST4CMP2V")]
pub type St4cmp2v = crate::Reg<st4cmp2v::St4cmp2vSpec>;
#[doc = "SHRTIMER Slave_TIMERx compare 2 value register"]
pub mod st4cmp2v;
#[doc = "ST4CMP3V (rw) register accessor: SHRTIMER Slave_TIMERx compare 3 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4cmp3v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4cmp3v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4cmp3v`]
module"]
#[doc(alias = "ST4CMP3V")]
pub type St4cmp3v = crate::Reg<st4cmp3v::St4cmp3vSpec>;
#[doc = "SHRTIMER Slave_TIMERx compare 3 value register"]
pub mod st4cmp3v;
#[doc = "ST4CAP0V (rw) register accessor: SHRTIMER Slave_TIMERx capture 0 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4cap0v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4cap0v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4cap0v`]
module"]
#[doc(alias = "ST4CAP0V")]
pub type St4cap0v = crate::Reg<st4cap0v::St4cap0vSpec>;
#[doc = "SHRTIMER Slave_TIMERx capture 0 value register"]
pub mod st4cap0v;
#[doc = "ST4CAP1V (rw) register accessor: SHRTIMER Slave_TIMERx capture 1 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4cap1v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4cap1v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4cap1v`]
module"]
#[doc(alias = "ST4CAP1V")]
pub type St4cap1v = crate::Reg<st4cap1v::St4cap1vSpec>;
#[doc = "SHRTIMER Slave_TIMERx capture 1 value register"]
pub mod st4cap1v;
#[doc = "ST4DTCTL (rw) register accessor: SHRTIMER Slave_TIMERx dead-time control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4dtctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4dtctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4dtctl`]
module"]
#[doc(alias = "ST4DTCTL")]
pub type St4dtctl = crate::Reg<st4dtctl::St4dtctlSpec>;
#[doc = "SHRTIMER Slave_TIMERx dead-time control register"]
pub mod st4dtctl;
#[doc = "ST4CH0SET (rw) register accessor: SHRTIMER Slave_TIMERx channel 0 set request register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4ch0set::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4ch0set::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4ch0set`]
module"]
#[doc(alias = "ST4CH0SET")]
pub type St4ch0set = crate::Reg<st4ch0set::St4ch0setSpec>;
#[doc = "SHRTIMER Slave_TIMERx channel 0 set request register"]
pub mod st4ch0set;
#[doc = "ST4CH0RST (rw) register accessor: SHRTIMER Slave_TIMERx channel 0 reset request register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4ch0rst::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4ch0rst::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4ch0rst`]
module"]
#[doc(alias = "ST4CH0RST")]
pub type St4ch0rst = crate::Reg<st4ch0rst::St4ch0rstSpec>;
#[doc = "SHRTIMER Slave_TIMERx channel 0 reset request register"]
pub mod st4ch0rst;
#[doc = "ST4CH1SET (rw) register accessor: SHRTIMER Slave_TIMERx channel 1 set request register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4ch1set::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4ch1set::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4ch1set`]
module"]
#[doc(alias = "ST4CH1SET")]
pub type St4ch1set = crate::Reg<st4ch1set::St4ch1setSpec>;
#[doc = "SHRTIMER Slave_TIMERx channel 1 set request register"]
pub mod st4ch1set;
#[doc = "ST4CH1RST (rw) register accessor: SHRTIMER Slave_TIMERx channel 1 reset request register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4ch1rst::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4ch1rst::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4ch1rst`]
module"]
#[doc(alias = "ST4CH1RST")]
pub type St4ch1rst = crate::Reg<st4ch1rst::St4ch1rstSpec>;
#[doc = "SHRTIMER Slave_TIMERx channel 1 reset request register"]
pub mod st4ch1rst;
#[doc = "ST4EXEVFCFG0 (rw) register accessor: SHRTIMER Slave_TIMERx external event filter configuration register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4exevfcfg0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4exevfcfg0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4exevfcfg0`]
module"]
#[doc(alias = "ST4EXEVFCFG0")]
pub type St4exevfcfg0 = crate::Reg<st4exevfcfg0::St4exevfcfg0Spec>;
#[doc = "SHRTIMER Slave_TIMERx external event filter configuration register 0"]
pub mod st4exevfcfg0;
#[doc = "ST4EXEVFCFG1 (rw) register accessor: SHRTIMER Slave_TIMERx external event filter configuration register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4exevfcfg1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4exevfcfg1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4exevfcfg1`]
module"]
#[doc(alias = "ST4EXEVFCFG1")]
pub type St4exevfcfg1 = crate::Reg<st4exevfcfg1::St4exevfcfg1Spec>;
#[doc = "SHRTIMER Slave_TIMERx external event filter configuration register 1"]
pub mod st4exevfcfg1;
#[doc = "ST4CNTRST (rw) register accessor: SHRTIMER Slave_TIMERx counter reset register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4cntrst::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4cntrst::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4cntrst`]
module"]
#[doc(alias = "ST4CNTRST")]
pub type St4cntrst = crate::Reg<st4cntrst::St4cntrstSpec>;
#[doc = "SHRTIMER Slave_TIMERx counter reset register"]
pub mod st4cntrst;
#[doc = "ST4CSCTL (rw) register accessor: SHRTIMER Slave_TIMERx carrier-signal control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4csctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4csctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4csctl`]
module"]
#[doc(alias = "ST4CSCTL")]
pub type St4csctl = crate::Reg<st4csctl::St4csctlSpec>;
#[doc = "SHRTIMER Slave_TIMERx carrier-signal control register"]
pub mod st4csctl;
#[doc = "ST4CAP0TRG (rw) register accessor: SHRTIMER Slave_TIMERx capture 0 trigger register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4cap0trg::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4cap0trg::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4cap0trg`]
module"]
#[doc(alias = "ST4CAP0TRG")]
pub type St4cap0trg = crate::Reg<st4cap0trg::St4cap0trgSpec>;
#[doc = "SHRTIMER Slave_TIMERx capture 0 trigger register"]
pub mod st4cap0trg;
#[doc = "ST4CAP1TRG (rw) register accessor: SHRTIMER Slave_TIMERx capture 1 trigger register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4cap1trg::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4cap1trg::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4cap1trg`]
module"]
#[doc(alias = "ST4CAP1TRG")]
pub type St4cap1trg = crate::Reg<st4cap1trg::St4cap1trgSpec>;
#[doc = "SHRTIMER Slave_TIMERx capture 1 trigger register"]
pub mod st4cap1trg;
#[doc = "ST4CHOCTL (rw) register accessor: SHRTIMER Slave_TIMERx channel output control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4choctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4choctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4choctl`]
module"]
#[doc(alias = "ST4CHOCTL")]
pub type St4choctl = crate::Reg<st4choctl::St4choctlSpec>;
#[doc = "SHRTIMER Slave_TIMERx channel output control register"]
pub mod st4choctl;
#[doc = "ST4FLTCTL (rw) register accessor: SHRTIMER Slave_TIMERx fault control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4fltctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4fltctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4fltctl`]
module"]
#[doc(alias = "ST4FLTCTL")]
pub type St4fltctl = crate::Reg<st4fltctl::St4fltctlSpec>;
#[doc = "SHRTIMER Slave_TIMERx fault control register"]
pub mod st4fltctl;
#[doc = "ST4ACTL (rw) register accessor: SHRTIMER Slave_TIMERx additional control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4actl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4actl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st4actl`]
module"]
#[doc(alias = "ST4ACTL")]
pub type St4actl = crate::Reg<st4actl::St4actlSpec>;
#[doc = "SHRTIMER Slave_TIMERx additional control register"]
pub mod st4actl;
