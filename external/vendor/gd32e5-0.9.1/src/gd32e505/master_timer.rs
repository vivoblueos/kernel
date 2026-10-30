#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    mtctl0: Mtctl0,
    mtintf: Mtintf,
    mtintc: Mtintc,
    mtdmainten: Mtdmainten,
    mtcnt: Mtcnt,
    mtcar: Mtcar,
    mtcrep: Mtcrep,
    mtcmp0v: Mtcmp0v,
    _reserved8: [u8; 0x04],
    mtcmp1v: Mtcmp1v,
    mtcmp2v: Mtcmp2v,
    mtcmp3v: Mtcmp3v,
    _reserved11: [u8; 0x4c],
    mtactl: Mtactl,
}
impl RegisterBlock {
    #[doc = "0x00 - SHRTIMER Master_TIMER control register 0"]
    #[inline(always)]
    pub const fn mtctl0(&self) -> &Mtctl0 {
        &self.mtctl0
    }
    #[doc = "0x04 - SHRTIMER Master_TIMER interrupt flag register"]
    #[inline(always)]
    pub const fn mtintf(&self) -> &Mtintf {
        &self.mtintf
    }
    #[doc = "0x08 - SHRTIMER Master_TIMER interrupt flag clear register"]
    #[inline(always)]
    pub const fn mtintc(&self) -> &Mtintc {
        &self.mtintc
    }
    #[doc = "0x0c - SHRTIMER Master_TIMER DMA and interrupt enable register"]
    #[inline(always)]
    pub const fn mtdmainten(&self) -> &Mtdmainten {
        &self.mtdmainten
    }
    #[doc = "0x10 - SHRTIMER Master_TIMER counter register"]
    #[inline(always)]
    pub const fn mtcnt(&self) -> &Mtcnt {
        &self.mtcnt
    }
    #[doc = "0x14 - SHRTIMER Master_TIMER counter auto reload register"]
    #[inline(always)]
    pub const fn mtcar(&self) -> &Mtcar {
        &self.mtcar
    }
    #[doc = "0x18 - SHRTIMER Master_TIMER counter repetition register"]
    #[inline(always)]
    pub const fn mtcrep(&self) -> &Mtcrep {
        &self.mtcrep
    }
    #[doc = "0x1c - SHRTIMER Master_TIMER compare 0 value register"]
    #[inline(always)]
    pub const fn mtcmp0v(&self) -> &Mtcmp0v {
        &self.mtcmp0v
    }
    #[doc = "0x24 - SHRTIMER Master_TIMER compare 1 value register"]
    #[inline(always)]
    pub const fn mtcmp1v(&self) -> &Mtcmp1v {
        &self.mtcmp1v
    }
    #[doc = "0x28 - SHRTIMER Master_TIMER compare 2 value register"]
    #[inline(always)]
    pub const fn mtcmp2v(&self) -> &Mtcmp2v {
        &self.mtcmp2v
    }
    #[doc = "0x2c - SHRTIMER Master_TIMER compare 3 value register"]
    #[inline(always)]
    pub const fn mtcmp3v(&self) -> &Mtcmp3v {
        &self.mtcmp3v
    }
    #[doc = "0x7c - SHRTIMER Master_TIMER additional control register"]
    #[inline(always)]
    pub const fn mtactl(&self) -> &Mtactl {
        &self.mtactl
    }
}
#[doc = "MTCTL0 (rw) register accessor: SHRTIMER Master_TIMER control register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mtctl0::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mtctl0::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mtctl0`]
module"]
#[doc(alias = "MTCTL0")]
pub type Mtctl0 = crate::Reg<mtctl0::Mtctl0Spec>;
#[doc = "SHRTIMER Master_TIMER control register 0"]
pub mod mtctl0;
#[doc = "MTINTF (r) register accessor: SHRTIMER Master_TIMER interrupt flag register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mtintf::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mtintf`]
module"]
#[doc(alias = "MTINTF")]
pub type Mtintf = crate::Reg<mtintf::MtintfSpec>;
#[doc = "SHRTIMER Master_TIMER interrupt flag register"]
pub mod mtintf;
#[doc = "MTINTC (w) register accessor: SHRTIMER Master_TIMER interrupt flag clear register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mtintc::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mtintc`]
module"]
#[doc(alias = "MTINTC")]
pub type Mtintc = crate::Reg<mtintc::MtintcSpec>;
#[doc = "SHRTIMER Master_TIMER interrupt flag clear register"]
pub mod mtintc;
#[doc = "MTDMAINTEN (rw) register accessor: SHRTIMER Master_TIMER DMA and interrupt enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mtdmainten::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mtdmainten::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mtdmainten`]
module"]
#[doc(alias = "MTDMAINTEN")]
pub type Mtdmainten = crate::Reg<mtdmainten::MtdmaintenSpec>;
#[doc = "SHRTIMER Master_TIMER DMA and interrupt enable register"]
pub mod mtdmainten;
#[doc = "MTCNT (rw) register accessor: SHRTIMER Master_TIMER counter register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mtcnt::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mtcnt::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mtcnt`]
module"]
#[doc(alias = "MTCNT")]
pub type Mtcnt = crate::Reg<mtcnt::MtcntSpec>;
#[doc = "SHRTIMER Master_TIMER counter register"]
pub mod mtcnt;
#[doc = "MTCAR (rw) register accessor: SHRTIMER Master_TIMER counter auto reload register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mtcar::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mtcar::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mtcar`]
module"]
#[doc(alias = "MTCAR")]
pub type Mtcar = crate::Reg<mtcar::MtcarSpec>;
#[doc = "SHRTIMER Master_TIMER counter auto reload register"]
pub mod mtcar;
#[doc = "MTCREP (rw) register accessor: SHRTIMER Master_TIMER counter repetition register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mtcrep::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mtcrep::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mtcrep`]
module"]
#[doc(alias = "MTCREP")]
pub type Mtcrep = crate::Reg<mtcrep::MtcrepSpec>;
#[doc = "SHRTIMER Master_TIMER counter repetition register"]
pub mod mtcrep;
#[doc = "MTCMP0V (rw) register accessor: SHRTIMER Master_TIMER compare 0 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mtcmp0v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mtcmp0v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mtcmp0v`]
module"]
#[doc(alias = "MTCMP0V")]
pub type Mtcmp0v = crate::Reg<mtcmp0v::Mtcmp0vSpec>;
#[doc = "SHRTIMER Master_TIMER compare 0 value register"]
pub mod mtcmp0v;
#[doc = "MTCMP1V (rw) register accessor: SHRTIMER Master_TIMER compare 1 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mtcmp1v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mtcmp1v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mtcmp1v`]
module"]
#[doc(alias = "MTCMP1V")]
pub type Mtcmp1v = crate::Reg<mtcmp1v::Mtcmp1vSpec>;
#[doc = "SHRTIMER Master_TIMER compare 1 value register"]
pub mod mtcmp1v;
#[doc = "MTCMP2V (rw) register accessor: SHRTIMER Master_TIMER compare 2 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mtcmp2v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mtcmp2v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mtcmp2v`]
module"]
#[doc(alias = "MTCMP2V")]
pub type Mtcmp2v = crate::Reg<mtcmp2v::Mtcmp2vSpec>;
#[doc = "SHRTIMER Master_TIMER compare 2 value register"]
pub mod mtcmp2v;
#[doc = "MTCMP3V (rw) register accessor: SHRTIMER Master_TIMER compare 3 value register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mtcmp3v::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mtcmp3v::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mtcmp3v`]
module"]
#[doc(alias = "MTCMP3V")]
pub type Mtcmp3v = crate::Reg<mtcmp3v::Mtcmp3vSpec>;
#[doc = "SHRTIMER Master_TIMER compare 3 value register"]
pub mod mtcmp3v;
#[doc = "MTACTL (rw) register accessor: SHRTIMER Master_TIMER additional control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mtactl::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`mtactl::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mtactl`]
module"]
#[doc(alias = "MTACTL")]
pub type Mtactl = crate::Reg<mtactl::MtactlSpec>;
#[doc = "SHRTIMER Master_TIMER additional control register"]
pub mod mtactl;
