#[repr(C)]
#[doc = "Register block"]
pub struct RegisterBlock {
    init: Init,
    rcmd: Rcmd,
    wcmd: Wcmd,
    idl: Idl,
    idh: Idh,
}
impl RegisterBlock {
    #[doc = "0x00 - SQPI Initial Register"]
    #[inline(always)]
    pub const fn init(&self) -> &Init {
        &self.init
    }
    #[doc = "0x04 - SQPI Read Command Register"]
    #[inline(always)]
    pub const fn rcmd(&self) -> &Rcmd {
        &self.rcmd
    }
    #[doc = "0x08 - Write Command Register"]
    #[inline(always)]
    pub const fn wcmd(&self) -> &Wcmd {
        &self.wcmd
    }
    #[doc = "0x0c - ID Low Register"]
    #[inline(always)]
    pub const fn idl(&self) -> &Idl {
        &self.idl
    }
    #[doc = "0x10 - ID High Register"]
    #[inline(always)]
    pub const fn idh(&self) -> &Idh {
        &self.idh
    }
}
#[doc = "INIT (rw) register accessor: SQPI Initial Register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`init::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`init::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@init`]
module"]
#[doc(alias = "INIT")]
pub type Init = crate::Reg<init::InitSpec>;
#[doc = "SQPI Initial Register"]
pub mod init;
#[doc = "RCMD (rw) register accessor: SQPI Read Command Register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rcmd::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`rcmd::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rcmd`]
module"]
#[doc(alias = "RCMD")]
pub type Rcmd = crate::Reg<rcmd::RcmdSpec>;
#[doc = "SQPI Read Command Register"]
pub mod rcmd;
#[doc = "WCMD (rw) register accessor: Write Command Register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`wcmd::R`].  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`wcmd::W`]. You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@wcmd`]
module"]
#[doc(alias = "WCMD")]
pub type Wcmd = crate::Reg<wcmd::WcmdSpec>;
#[doc = "Write Command Register"]
pub mod wcmd;
#[doc = "IDL (r) register accessor: ID Low Register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`idl::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@idl`]
module"]
#[doc(alias = "IDL")]
pub type Idl = crate::Reg<idl::IdlSpec>;
#[doc = "ID Low Register"]
pub mod idl;
#[doc = "IDH (r) register accessor: ID High Register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`idh::R`].  See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@idh`]
module"]
#[doc(alias = "IDH")]
pub type Idh = crate::Reg<idh::IdhSpec>;
#[doc = "ID High Register"]
pub mod idh;
