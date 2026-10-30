#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    ctl0: Ctl0,
    ctl1: Ctl1,
    saddr0: Saddr0,
    saddr1: Saddr1,
    data: Data,
    stat0: Stat0,
    stat1: Stat1,
    ckcfg: Ckcfg,
    rt: Rt,
    _reserved9: [u8; 0x5c],
    samcs: Samcs,
    _reserved10: [u8; 0x0c],
    ctl2: Ctl2,
    cs: Cs,
    statc: Statc,
}
impl RegisterBlock {
    #[doc = "0x00 - Control register 0"]
    #[inline(always)]
    pub const fn ctl0(&self) -> &Ctl0 {
        &self.ctl0
    }
    #[doc = "0x04 - Control register 1"]
    #[inline(always)]
    pub const fn ctl1(&self) -> &Ctl1 {
        &self.ctl1
    }
    #[doc = "0x08 - Slave address register 0"]
    #[inline(always)]
    pub const fn saddr0(&self) -> &Saddr0 {
        &self.saddr0
    }
    #[doc = "0x0c - Slave address register 1"]
    #[inline(always)]
    pub const fn saddr1(&self) -> &Saddr1 {
        &self.saddr1
    }
    #[doc = "0x10 - Transfer buffer register"]
    #[inline(always)]
    pub const fn data(&self) -> &Data {
        &self.data
    }
    #[doc = "0x14 - Transfer status register 0"]
    #[inline(always)]
    pub const fn stat0(&self) -> &Stat0 {
        &self.stat0
    }
    #[doc = "0x18 - Transfer status register 1"]
    #[inline(always)]
    pub const fn stat1(&self) -> &Stat1 {
        &self.stat1
    }
    #[doc = "0x1c - Clock configure register"]
    #[inline(always)]
    pub const fn ckcfg(&self) -> &Ckcfg {
        &self.ckcfg
    }
    #[doc = "0x20 - Rise time register"]
    #[inline(always)]
    pub const fn rt(&self) -> &Rt {
        &self.rt
    }
    #[doc = "0x80 - SAM control and status register"]
    #[inline(always)]
    pub const fn samcs(&self) -> &Samcs {
        &self.samcs
    }
    #[doc = "0x90 - Control register 2"]
    #[inline(always)]
    pub const fn ctl2(&self) -> &Ctl2 {
        &self.ctl2
    }
    #[doc = "0x94 - Control and status register"]
    #[inline(always)]
    pub const fn cs(&self) -> &Cs {
        &self.cs
    }
    #[doc = "0x98 - Status clear register"]
    #[inline(always)]
    pub const fn statc(&self) -> &Statc {
        &self.statc
    }
}
#[doc = "CTL0 (rw) register accessor: Control register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ctl0`]
module"]
#[doc(alias = "CTL0")]
pub type Ctl0 = crate::Reg<ctl0::Ctl0Spec>;
#[doc = "Control register 0"]
pub mod ctl0;
#[doc = "CTL1 (rw) register accessor: Control register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ctl1`]
module"]
#[doc(alias = "CTL1")]
pub type Ctl1 = crate::Reg<ctl1::Ctl1Spec>;
#[doc = "Control register 1"]
pub mod ctl1;
#[doc = "SADDR0 (rw) register accessor: Slave address register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`saddr0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`saddr0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@saddr0`]
module"]
#[doc(alias = "SADDR0")]
pub type Saddr0 = crate::Reg<saddr0::Saddr0Spec>;
#[doc = "Slave address register 0"]
pub mod saddr0;
#[doc = "SADDR1 (rw) register accessor: Slave address register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`saddr1::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`saddr1::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@saddr1`]
module"]
#[doc(alias = "SADDR1")]
pub type Saddr1 = crate::Reg<saddr1::Saddr1Spec>;
#[doc = "Slave address register 1"]
pub mod saddr1;
#[doc = "DATA (rw) register accessor: Transfer buffer register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data`]
module"]
#[doc(alias = "DATA")]
pub type Data = crate::Reg<data::DataSpec>;
#[doc = "Transfer buffer register"]
pub mod data;
#[doc = "STAT0 (rw) register accessor: Transfer status register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`stat0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`stat0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@stat0`]
module"]
#[doc(alias = "STAT0")]
pub type Stat0 = crate::Reg<stat0::Stat0Spec>;
#[doc = "Transfer status register 0"]
pub mod stat0;
#[doc = "STAT1 (r) register accessor: Transfer status register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`stat1::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@stat1`]
module"]
#[doc(alias = "STAT1")]
pub type Stat1 = crate::Reg<stat1::Stat1Spec>;
#[doc = "Transfer status register 1"]
pub mod stat1;
#[doc = "CKCFG (rw) register accessor: Clock configure register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ckcfg::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ckcfg::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ckcfg`]
module"]
#[doc(alias = "CKCFG")]
pub type Ckcfg = crate::Reg<ckcfg::CkcfgSpec>;
#[doc = "Clock configure register"]
pub mod ckcfg;
#[doc = "RT (rw) register accessor: Rise time register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rt::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`rt::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rt`]
module"]
#[doc(alias = "RT")]
pub type Rt = crate::Reg<rt::RtSpec>;
#[doc = "Rise time register"]
pub mod rt;
#[doc = "SAMCS (rw) register accessor: SAM control and status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`samcs::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`samcs::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@samcs`]
module"]
#[doc(alias = "SAMCS")]
pub type Samcs = crate::Reg<samcs::SamcsSpec>;
#[doc = "SAM control and status register"]
pub mod samcs;
#[doc = "CTL2 (rw) register accessor: Control register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl2::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl2::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ctl2`]
module"]
#[doc(alias = "CTL2")]
pub type Ctl2 = crate::Reg<ctl2::Ctl2Spec>;
#[doc = "Control register 2"]
pub mod ctl2;
#[doc = "CS (rw) register accessor: Control and status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`cs::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cs::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cs`]
module"]
#[doc(alias = "CS")]
pub type Cs = crate::Reg<cs::CsSpec>;
#[doc = "Control and status register"]
pub mod cs;
#[doc = "STATC (rw) register accessor: Status clear register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`statc::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`statc::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@statc`]
module"]
#[doc(alias = "STATC")]
pub type Statc = crate::Reg<statc::StatcSpec>;
#[doc = "Status clear register"]
pub mod statc;
