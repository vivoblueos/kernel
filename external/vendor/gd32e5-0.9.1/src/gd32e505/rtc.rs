#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    inten: Inten,
    ctl: Ctl,
    psch: Psch,
    pscl: Pscl,
    divh: Divh,
    divl: Divl,
    cnth: Cnth,
    cntl: Cntl,
    alrmh: Alrmh,
    alrml: Alrml,
}
impl RegisterBlock {
    #[doc = "0x00 - RTC interrupt enable register"]
    #[inline(always)]
    pub const fn inten(&self) -> &Inten {
        &self.inten
    }
    #[doc = "0x04 - control register"]
    #[inline(always)]
    pub const fn ctl(&self) -> &Ctl {
        &self.ctl
    }
    #[doc = "0x08 - RTC prescaler high register"]
    #[inline(always)]
    pub const fn psch(&self) -> &Psch {
        &self.psch
    }
    #[doc = "0x0c - RTC prescaler low register"]
    #[inline(always)]
    pub const fn pscl(&self) -> &Pscl {
        &self.pscl
    }
    #[doc = "0x10 - RTC divider high register"]
    #[inline(always)]
    pub const fn divh(&self) -> &Divh {
        &self.divh
    }
    #[doc = "0x14 - RTC divider low register"]
    #[inline(always)]
    pub const fn divl(&self) -> &Divl {
        &self.divl
    }
    #[doc = "0x18 - RTC counter high register"]
    #[inline(always)]
    pub const fn cnth(&self) -> &Cnth {
        &self.cnth
    }
    #[doc = "0x1c - RTC counter low register"]
    #[inline(always)]
    pub const fn cntl(&self) -> &Cntl {
        &self.cntl
    }
    #[doc = "0x20 - Alarm high register"]
    #[inline(always)]
    pub const fn alrmh(&self) -> &Alrmh {
        &self.alrmh
    }
    #[doc = "0x24 - RTC alarm low register"]
    #[inline(always)]
    pub const fn alrml(&self) -> &Alrml {
        &self.alrml
    }
}
#[doc = "INTEN (rw) register accessor: RTC interrupt enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`inten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`inten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@inten`]
module"]
#[doc(alias = "INTEN")]
pub type Inten = crate::Reg<inten::IntenSpec>;
#[doc = "RTC interrupt enable register"]
pub mod inten;
#[doc = "CTL (rw) register accessor: control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ctl`]
module"]
#[doc(alias = "CTL")]
pub type Ctl = crate::Reg<ctl::CtlSpec>;
#[doc = "control register"]
pub mod ctl;
#[doc = "PSCH (w) register accessor: RTC prescaler high register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`psch::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@psch`]
module"]
#[doc(alias = "PSCH")]
pub type Psch = crate::Reg<psch::PschSpec>;
#[doc = "RTC prescaler high register"]
pub mod psch;
#[doc = "PSCL (w) register accessor: RTC prescaler low register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`pscl::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pscl`]
module"]
#[doc(alias = "PSCL")]
pub type Pscl = crate::Reg<pscl::PsclSpec>;
#[doc = "RTC prescaler low register"]
pub mod pscl;
#[doc = "DIVH (r) register accessor: RTC divider high register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`divh::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@divh`]
module"]
#[doc(alias = "DIVH")]
pub type Divh = crate::Reg<divh::DivhSpec>;
#[doc = "RTC divider high register"]
pub mod divh;
#[doc = "DIVL (r) register accessor: RTC divider low register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`divl::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@divl`]
module"]
#[doc(alias = "DIVL")]
pub type Divl = crate::Reg<divl::DivlSpec>;
#[doc = "RTC divider low register"]
pub mod divl;
#[doc = "CNTH (rw) register accessor: RTC counter high register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`cnth::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cnth::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cnth`]
module"]
#[doc(alias = "CNTH")]
pub type Cnth = crate::Reg<cnth::CnthSpec>;
#[doc = "RTC counter high register"]
pub mod cnth;
#[doc = "CNTL (rw) register accessor: RTC counter low register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`cntl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`cntl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cntl`]
module"]
#[doc(alias = "CNTL")]
pub type Cntl = crate::Reg<cntl::CntlSpec>;
#[doc = "RTC counter low register"]
pub mod cntl;
#[doc = "ALRMH (w) register accessor: Alarm high register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`alrmh::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@alrmh`]
module"]
#[doc(alias = "ALRMH")]
pub type Alrmh = crate::Reg<alrmh::AlrmhSpec>;
#[doc = "Alarm high register"]
pub mod alrmh;
#[doc = "ALRML (w) register accessor: RTC alarm low register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`alrml::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@alrml`]
module"]
#[doc(alias = "ALRML")]
pub type Alrml = crate::Reg<alrml::AlrmlSpec>;
#[doc = "RTC alarm low register"]
pub mod alrml;
