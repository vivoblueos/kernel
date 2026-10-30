#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Cluster REGION%s, containing REGION*_ADDR_START, REGION*_ADDR_END, REGION*_PMS_ATTR"]
pub struct REGION {
    addr_start: ADDR_START,
    addr_end: ADDR_END,
    pms_attr: PMS_ATTR,
}
impl REGION {
    #[doc = "0x00 - Region address register"]
    #[inline(always)]
    pub const fn addr_start(&self) -> &ADDR_START {
        &self.addr_start
    }
    #[doc = "0x04 - Region address register"]
    #[inline(always)]
    pub const fn addr_end(&self) -> &ADDR_END {
        &self.addr_end
    }
    #[doc = "0x08 - Region access authority attribute register"]
    #[inline(always)]
    pub const fn pms_attr(&self) -> &PMS_ATTR {
        &self.pms_attr
    }
}
#[doc = "ADDR_START (rw) register accessor: Region address register\n\nYou can [`read`](crate::Reg::read) this register and get [`addr_start::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`addr_start::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@addr_start`] module"]
pub type ADDR_START = crate::Reg<addr_start::ADDR_START_SPEC>;
#[doc = "Region address register"]
pub mod addr_start;
#[doc = "ADDR_END (rw) register accessor: Region address register\n\nYou can [`read`](crate::Reg::read) this register and get [`addr_end::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`addr_end::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@addr_end`] module"]
pub type ADDR_END = crate::Reg<addr_end::ADDR_END_SPEC>;
#[doc = "Region address register"]
pub mod addr_end;
#[doc = "PMS_ATTR (rw) register accessor: Region access authority attribute register\n\nYou can [`read`](crate::Reg::read) this register and get [`pms_attr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pms_attr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pms_attr`] module"]
pub type PMS_ATTR = crate::Reg<pms_attr::PMS_ATTR_SPEC>;
#[doc = "Region access authority attribute register"]
pub mod pms_attr;
