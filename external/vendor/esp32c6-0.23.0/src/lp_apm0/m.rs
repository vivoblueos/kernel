#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Cluster M%s, containing M?_STATUS, M?_STATUS_CLR, M?_EXCEPTION_INFO0, M?_EXCEPTION_INFO1"]
pub struct M {
    status: STATUS,
    status_clr: STATUS_CLR,
    exception_info0: EXCEPTION_INFO0,
    exception_info1: EXCEPTION_INFO1,
}
impl M {
    #[doc = "0x00 - M0 status register"]
    #[inline(always)]
    pub const fn status(&self) -> &STATUS {
        &self.status
    }
    #[doc = "0x04 - M0 status clear register"]
    #[inline(always)]
    pub const fn status_clr(&self) -> &STATUS_CLR {
        &self.status_clr
    }
    #[doc = "0x08 - M0 exception_info0 register"]
    #[inline(always)]
    pub const fn exception_info0(&self) -> &EXCEPTION_INFO0 {
        &self.exception_info0
    }
    #[doc = "0x0c - M0 exception_info1 register"]
    #[inline(always)]
    pub const fn exception_info1(&self) -> &EXCEPTION_INFO1 {
        &self.exception_info1
    }
}
#[doc = "STATUS (r) register accessor: M0 status register\n\nYou can [`read`](crate::Reg::read) this register and get [`status::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@status`] module"]
pub type STATUS = crate::Reg<status::STATUS_SPEC>;
#[doc = "M0 status register"]
pub mod status;
#[doc = "STATUS_CLR (w) register accessor: M0 status clear register\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`status_clr::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@status_clr`] module"]
pub type STATUS_CLR = crate::Reg<status_clr::STATUS_CLR_SPEC>;
#[doc = "M0 status clear register"]
pub mod status_clr;
#[doc = "EXCEPTION_INFO0 (r) register accessor: M0 exception_info0 register\n\nYou can [`read`](crate::Reg::read) this register and get [`exception_info0::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@exception_info0`] module"]
pub type EXCEPTION_INFO0 = crate::Reg<exception_info0::EXCEPTION_INFO0_SPEC>;
#[doc = "M0 exception_info0 register"]
pub mod exception_info0;
#[doc = "EXCEPTION_INFO1 (r) register accessor: M0 exception_info1 register\n\nYou can [`read`](crate::Reg::read) this register and get [`exception_info1::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@exception_info1`] module"]
pub type EXCEPTION_INFO1 = crate::Reg<exception_info1::EXCEPTION_INFO1_SPEC>;
#[doc = "M0 exception_info1 register"]
pub mod exception_info1;
