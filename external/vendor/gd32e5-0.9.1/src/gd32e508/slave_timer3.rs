#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    st3ctl0: St3ctl0,
    st3intf: St3intf,
    st3intc: St3intc,
    st3dmainten: St3dmainten,
    st3cnt: St3cnt,
    st3car: St3car,
    st3crep: St3crep,
    st3cmp0v: St3cmp0v,
    st3cmp0cp: St3cmp0cp,
    st3cmp1v: St3cmp1v,
    st3cmp2v: St3cmp2v,
    st3cmp3v: St3cmp3v,
    st3cap0v: St3cap0v,
    st3cap1v: St3cap1v,
    st3dtctl: St3dtctl,
    st3ch0set: St3ch0set,
    st3ch0rst: St3ch0rst,
    st3ch1set: St3ch1set,
    st3ch1rst: St3ch1rst,
    st3exevfcfg0: St3exevfcfg0,
    st3exevfcfg1: St3exevfcfg1,
    st3cntrst: St3cntrst,
    st3csctl: St3csctl,
    st3cap0trg: St3cap0trg,
    st3cap1trg: St3cap1trg,
    st3choctl: St3choctl,
    st3fltctl: St3fltctl,
    _reserved27: [u8; 0x10],
    st3actl: St3actl,
}
impl RegisterBlock {
    #[doc = "0x00 - SHRTIMER Slave_TIMERx control register 0"]
    #[inline(always)]
    pub const fn st3ctl0(&self) -> &St3ctl0 {
        &self.st3ctl0
    }
    #[doc = "0x04 - SHRTIMER Slave_TIMERx interrupt flag register"]
    #[inline(always)]
    pub const fn st3intf(&self) -> &St3intf {
        &self.st3intf
    }
    #[doc = "0x08 - SHRTIMER Slave_TIMERx interrupt flag clear register"]
    #[inline(always)]
    pub const fn st3intc(&self) -> &St3intc {
        &self.st3intc
    }
    #[doc = "0x0c - SHRTIMER Slave_TIMERx DMA and interrupt enable register"]
    #[inline(always)]
    pub const fn st3dmainten(&self) -> &St3dmainten {
        &self.st3dmainten
    }
    #[doc = "0x10 - SHRTIMER Slave_TIMERx counter register"]
    #[inline(always)]
    pub const fn st3cnt(&self) -> &St3cnt {
        &self.st3cnt
    }
    #[doc = "0x14 - SHRTIMER Slave_TIMER3 counter auto reload register"]
    #[inline(always)]
    pub const fn st3car(&self) -> &St3car {
        &self.st3car
    }
    #[doc = "0x18 - SHRTIMER Slave_TIMER3 counter repetition register"]
    #[inline(always)]
    pub const fn st3crep(&self) -> &St3crep {
        &self.st3crep
    }
    #[doc = "0x1c - SHRTIMER Slave_TIMER3 compare 0 value register"]
    #[inline(always)]
    pub const fn st3cmp0v(&self) -> &St3cmp0v {
        &self.st3cmp0v
    }
    #[doc = "0x20 - SHRTIMER Slave_TIMERx compare 0 composite register"]
    #[inline(always)]
    pub const fn st3cmp0cp(&self) -> &St3cmp0cp {
        &self.st3cmp0cp
    }
    #[doc = "0x24 - SHRTIMER Slave_TIMERx compare 1 value register"]
    #[inline(always)]
    pub const fn st3cmp1v(&self) -> &St3cmp1v {
        &self.st3cmp1v
    }
    #[doc = "0x28 - SHRTIMER Slave_TIMERx compare 2 value register"]
    #[inline(always)]
    pub const fn st3cmp2v(&self) -> &St3cmp2v {
        &self.st3cmp2v
    }
    #[doc = "0x2c - SHRTIMER Slave_TIMERx compare 3 value register"]
    #[inline(always)]
    pub const fn st3cmp3v(&self) -> &St3cmp3v {
        &self.st3cmp3v
    }
    #[doc = "0x30 - SHRTIMER Slave_TIMERx capture 0 value register"]
    #[inline(always)]
    pub const fn st3cap0v(&self) -> &St3cap0v {
        &self.st3cap0v
    }
    #[doc = "0x34 - SHRTIMER Slave_TIMERx capture 1 value register"]
    #[inline(always)]
    pub const fn st3cap1v(&self) -> &St3cap1v {
        &self.st3cap1v
    }
    #[doc = "0x38 - SHRTIMER Slave_TIMERx dead-time control register"]
    #[inline(always)]
    pub const fn st3dtctl(&self) -> &St3dtctl {
        &self.st3dtctl
    }
    #[doc = "0x3c - SHRTIMER Slave_TIMERx channel 0 set request register"]
    #[inline(always)]
    pub const fn st3ch0set(&self) -> &St3ch0set {
        &self.st3ch0set
    }
    #[doc = "0x40 - SHRTIMER Slave_TIMERx channel 0 reset request register"]
    #[inline(always)]
    pub const fn st3ch0rst(&self) -> &St3ch0rst {
        &self.st3ch0rst
    }
    #[doc = "0x44 - SHRTIMER Slave_TIMERx channel 1 set request register"]
    #[inline(always)]
    pub const fn st3ch1set(&self) -> &St3ch1set {
        &self.st3ch1set
    }
    #[doc = "0x48 - SHRTIMER Slave_TIMERx channel 1 reset request register"]
    #[inline(always)]
    pub const fn st3ch1rst(&self) -> &St3ch1rst {
        &self.st3ch1rst
    }
    #[doc = "0x4c - SHRTIMER Slave_TIMERx external event filter configuration register 0"]
    #[inline(always)]
    pub const fn st3exevfcfg0(&self) -> &St3exevfcfg0 {
        &self.st3exevfcfg0
    }
    #[doc = "0x50 - SHRTIMER Slave_TIMERx external event filter configuration register 1"]
    #[inline(always)]
    pub const fn st3exevfcfg1(&self) -> &St3exevfcfg1 {
        &self.st3exevfcfg1
    }
    #[doc = "0x54 - SHRTIMER Slave_TIMERx counter reset register"]
    #[inline(always)]
    pub const fn st3cntrst(&self) -> &St3cntrst {
        &self.st3cntrst
    }
    #[doc = "0x58 - SHRTIMER Slave_TIMERx carrier-signal control register"]
    #[inline(always)]
    pub const fn st3csctl(&self) -> &St3csctl {
        &self.st3csctl
    }
    #[doc = "0x5c - SHRTIMER Slave_TIMERx capture 0 trigger register"]
    #[inline(always)]
    pub const fn st3cap0trg(&self) -> &St3cap0trg {
        &self.st3cap0trg
    }
    #[doc = "0x60 - SHRTIMER Slave_TIMERx capture 1 trigger register"]
    #[inline(always)]
    pub const fn st3cap1trg(&self) -> &St3cap1trg {
        &self.st3cap1trg
    }
    #[doc = "0x64 - SHRTIMER Slave_TIMERx channel output control register"]
    #[inline(always)]
    pub const fn st3choctl(&self) -> &St3choctl {
        &self.st3choctl
    }
    #[doc = "0x68 - SHRTIMER Slave_TIMERx fault control register"]
    #[inline(always)]
    pub const fn st3fltctl(&self) -> &St3fltctl {
        &self.st3fltctl
    }
    #[doc = "0x7c - SHRTIMER Slave_TIMERx additional control register"]
    #[inline(always)]
    pub const fn st3actl(&self) -> &St3actl {
        &self.st3actl
    }
}
#[doc = "ST3CTL0 (rw) register accessor: SHRTIMER Slave_TIMERx control register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3ctl0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3ctl0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3ctl0`]
module"]
#[doc(alias = "ST3CTL0")]
pub type St3ctl0 = crate::Reg<st3ctl0::St3ctl0Spec>;
#[doc = "SHRTIMER Slave_TIMERx control register 0"]
pub mod st3ctl0;
#[doc = "ST3INTF (r) register accessor: SHRTIMER Slave_TIMERx interrupt flag register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3intf::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3intf`]
module"]
#[doc(alias = "ST3INTF")]
pub type St3intf = crate::Reg<st3intf::St3intfSpec>;
#[doc = "SHRTIMER Slave_TIMERx interrupt flag register"]
pub mod st3intf;
#[doc = "ST3INTC (w) register accessor: SHRTIMER Slave_TIMERx interrupt flag clear register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3intc::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3intc`]
module"]
#[doc(alias = "ST3INTC")]
pub type St3intc = crate::Reg<st3intc::St3intcSpec>;
#[doc = "SHRTIMER Slave_TIMERx interrupt flag clear register"]
pub mod st3intc;
#[doc = "ST3DMAINTEN (rw) register accessor: SHRTIMER Slave_TIMERx DMA and interrupt enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3dmainten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3dmainten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3dmainten`]
module"]
#[doc(alias = "ST3DMAINTEN")]
pub type St3dmainten = crate::Reg<st3dmainten::St3dmaintenSpec>;
#[doc = "SHRTIMER Slave_TIMERx DMA and interrupt enable register"]
pub mod st3dmainten;
#[doc = "ST3CNT (rw) register accessor: SHRTIMER Slave_TIMERx counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3cnt::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3cnt::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3cnt`]
module"]
#[doc(alias = "ST3CNT")]
pub type St3cnt = crate::Reg<st3cnt::St3cntSpec>;
#[doc = "SHRTIMER Slave_TIMERx counter register"]
pub mod st3cnt;
#[doc = "ST3CAR (rw) register accessor: SHRTIMER Slave_TIMER3 counter auto reload register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3car::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3car::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3car`]
module"]
#[doc(alias = "ST3CAR")]
pub type St3car = crate::Reg<st3car::St3carSpec>;
#[doc = "SHRTIMER Slave_TIMER3 counter auto reload register"]
pub mod st3car;
#[doc = "ST3CREP (rw) register accessor: SHRTIMER Slave_TIMER3 counter repetition register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3crep::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3crep::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3crep`]
module"]
#[doc(alias = "ST3CREP")]
pub type St3crep = crate::Reg<st3crep::St3crepSpec>;
#[doc = "SHRTIMER Slave_TIMER3 counter repetition register"]
pub mod st3crep;
#[doc = "ST3CMP0V (rw) register accessor: SHRTIMER Slave_TIMER3 compare 0 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3cmp0v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3cmp0v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3cmp0v`]
module"]
#[doc(alias = "ST3CMP0V")]
pub type St3cmp0v = crate::Reg<st3cmp0v::St3cmp0vSpec>;
#[doc = "SHRTIMER Slave_TIMER3 compare 0 value register"]
pub mod st3cmp0v;
#[doc = "ST3CMP0CP (rw) register accessor: SHRTIMER Slave_TIMERx compare 0 composite register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3cmp0cp::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3cmp0cp::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3cmp0cp`]
module"]
#[doc(alias = "ST3CMP0CP")]
pub type St3cmp0cp = crate::Reg<st3cmp0cp::St3cmp0cpSpec>;
#[doc = "SHRTIMER Slave_TIMERx compare 0 composite register"]
pub mod st3cmp0cp;
#[doc = "ST3CMP1V (rw) register accessor: SHRTIMER Slave_TIMERx compare 1 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3cmp1v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3cmp1v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3cmp1v`]
module"]
#[doc(alias = "ST3CMP1V")]
pub type St3cmp1v = crate::Reg<st3cmp1v::St3cmp1vSpec>;
#[doc = "SHRTIMER Slave_TIMERx compare 1 value register"]
pub mod st3cmp1v;
#[doc = "ST3CMP2V (rw) register accessor: SHRTIMER Slave_TIMERx compare 2 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3cmp2v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3cmp2v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3cmp2v`]
module"]
#[doc(alias = "ST3CMP2V")]
pub type St3cmp2v = crate::Reg<st3cmp2v::St3cmp2vSpec>;
#[doc = "SHRTIMER Slave_TIMERx compare 2 value register"]
pub mod st3cmp2v;
#[doc = "ST3CMP3V (rw) register accessor: SHRTIMER Slave_TIMERx compare 3 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3cmp3v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3cmp3v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3cmp3v`]
module"]
#[doc(alias = "ST3CMP3V")]
pub type St3cmp3v = crate::Reg<st3cmp3v::St3cmp3vSpec>;
#[doc = "SHRTIMER Slave_TIMERx compare 3 value register"]
pub mod st3cmp3v;
#[doc = "ST3CAP0V (rw) register accessor: SHRTIMER Slave_TIMERx capture 0 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3cap0v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3cap0v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3cap0v`]
module"]
#[doc(alias = "ST3CAP0V")]
pub type St3cap0v = crate::Reg<st3cap0v::St3cap0vSpec>;
#[doc = "SHRTIMER Slave_TIMERx capture 0 value register"]
pub mod st3cap0v;
#[doc = "ST3CAP1V (rw) register accessor: SHRTIMER Slave_TIMERx capture 1 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3cap1v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3cap1v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3cap1v`]
module"]
#[doc(alias = "ST3CAP1V")]
pub type St3cap1v = crate::Reg<st3cap1v::St3cap1vSpec>;
#[doc = "SHRTIMER Slave_TIMERx capture 1 value register"]
pub mod st3cap1v;
#[doc = "ST3DTCTL (rw) register accessor: SHRTIMER Slave_TIMERx dead-time control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3dtctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3dtctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3dtctl`]
module"]
#[doc(alias = "ST3DTCTL")]
pub type St3dtctl = crate::Reg<st3dtctl::St3dtctlSpec>;
#[doc = "SHRTIMER Slave_TIMERx dead-time control register"]
pub mod st3dtctl;
#[doc = "ST3CH0SET (rw) register accessor: SHRTIMER Slave_TIMERx channel 0 set request register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3ch0set::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3ch0set::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3ch0set`]
module"]
#[doc(alias = "ST3CH0SET")]
pub type St3ch0set = crate::Reg<st3ch0set::St3ch0setSpec>;
#[doc = "SHRTIMER Slave_TIMERx channel 0 set request register"]
pub mod st3ch0set;
#[doc = "ST3CH0RST (rw) register accessor: SHRTIMER Slave_TIMERx channel 0 reset request register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3ch0rst::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3ch0rst::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3ch0rst`]
module"]
#[doc(alias = "ST3CH0RST")]
pub type St3ch0rst = crate::Reg<st3ch0rst::St3ch0rstSpec>;
#[doc = "SHRTIMER Slave_TIMERx channel 0 reset request register"]
pub mod st3ch0rst;
#[doc = "ST3CH1SET (rw) register accessor: SHRTIMER Slave_TIMERx channel 1 set request register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3ch1set::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3ch1set::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3ch1set`]
module"]
#[doc(alias = "ST3CH1SET")]
pub type St3ch1set = crate::Reg<st3ch1set::St3ch1setSpec>;
#[doc = "SHRTIMER Slave_TIMERx channel 1 set request register"]
pub mod st3ch1set;
#[doc = "ST3CH1RST (rw) register accessor: SHRTIMER Slave_TIMERx channel 1 reset request register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3ch1rst::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3ch1rst::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3ch1rst`]
module"]
#[doc(alias = "ST3CH1RST")]
pub type St3ch1rst = crate::Reg<st3ch1rst::St3ch1rstSpec>;
#[doc = "SHRTIMER Slave_TIMERx channel 1 reset request register"]
pub mod st3ch1rst;
#[doc = "ST3EXEVFCFG0 (rw) register accessor: SHRTIMER Slave_TIMERx external event filter configuration register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3exevfcfg0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3exevfcfg0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3exevfcfg0`]
module"]
#[doc(alias = "ST3EXEVFCFG0")]
pub type St3exevfcfg0 = crate::Reg<st3exevfcfg0::St3exevfcfg0Spec>;
#[doc = "SHRTIMER Slave_TIMERx external event filter configuration register 0"]
pub mod st3exevfcfg0;
#[doc = "ST3EXEVFCFG1 (rw) register accessor: SHRTIMER Slave_TIMERx external event filter configuration register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3exevfcfg1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3exevfcfg1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3exevfcfg1`]
module"]
#[doc(alias = "ST3EXEVFCFG1")]
pub type St3exevfcfg1 = crate::Reg<st3exevfcfg1::St3exevfcfg1Spec>;
#[doc = "SHRTIMER Slave_TIMERx external event filter configuration register 1"]
pub mod st3exevfcfg1;
#[doc = "ST3CNTRST (rw) register accessor: SHRTIMER Slave_TIMERx counter reset register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3cntrst::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3cntrst::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3cntrst`]
module"]
#[doc(alias = "ST3CNTRST")]
pub type St3cntrst = crate::Reg<st3cntrst::St3cntrstSpec>;
#[doc = "SHRTIMER Slave_TIMERx counter reset register"]
pub mod st3cntrst;
#[doc = "ST3CSCTL (rw) register accessor: SHRTIMER Slave_TIMERx carrier-signal control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3csctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3csctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3csctl`]
module"]
#[doc(alias = "ST3CSCTL")]
pub type St3csctl = crate::Reg<st3csctl::St3csctlSpec>;
#[doc = "SHRTIMER Slave_TIMERx carrier-signal control register"]
pub mod st3csctl;
#[doc = "ST3CAP0TRG (rw) register accessor: SHRTIMER Slave_TIMERx capture 0 trigger register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3cap0trg::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3cap0trg::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3cap0trg`]
module"]
#[doc(alias = "ST3CAP0TRG")]
pub type St3cap0trg = crate::Reg<st3cap0trg::St3cap0trgSpec>;
#[doc = "SHRTIMER Slave_TIMERx capture 0 trigger register"]
pub mod st3cap0trg;
#[doc = "ST3CAP1TRG (rw) register accessor: SHRTIMER Slave_TIMERx capture 1 trigger register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3cap1trg::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3cap1trg::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3cap1trg`]
module"]
#[doc(alias = "ST3CAP1TRG")]
pub type St3cap1trg = crate::Reg<st3cap1trg::St3cap1trgSpec>;
#[doc = "SHRTIMER Slave_TIMERx capture 1 trigger register"]
pub mod st3cap1trg;
#[doc = "ST3CHOCTL (rw) register accessor: SHRTIMER Slave_TIMERx channel output control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3choctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3choctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3choctl`]
module"]
#[doc(alias = "ST3CHOCTL")]
pub type St3choctl = crate::Reg<st3choctl::St3choctlSpec>;
#[doc = "SHRTIMER Slave_TIMERx channel output control register"]
pub mod st3choctl;
#[doc = "ST3FLTCTL (rw) register accessor: SHRTIMER Slave_TIMERx fault control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3fltctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3fltctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3fltctl`]
module"]
#[doc(alias = "ST3FLTCTL")]
pub type St3fltctl = crate::Reg<st3fltctl::St3fltctlSpec>;
#[doc = "SHRTIMER Slave_TIMERx fault control register"]
pub mod st3fltctl;
#[doc = "ST3ACTL (rw) register accessor: SHRTIMER Slave_TIMERx additional control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3actl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3actl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st3actl`]
module"]
#[doc(alias = "ST3ACTL")]
pub type St3actl = crate::Reg<st3actl::St3actlSpec>;
#[doc = "SHRTIMER Slave_TIMERx additional control register"]
pub mod st3actl;
