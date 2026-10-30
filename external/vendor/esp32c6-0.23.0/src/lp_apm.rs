#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    region_filter_en: REGION_FILTER_EN,
    region: [REGION; 4],
    _reserved2: [u8; 0x90],
    func_ctrl: FUNC_CTRL,
    m: [M; 2],
    int_en: INT_EN,
    clock_gate: CLOCK_GATE,
    _reserved6: [u8; 0x0c],
    date: DATE,
}
impl RegisterBlock {
    #[doc = "0x00 - Region filter enable register"]
    #[inline(always)]
    pub const fn region_filter_en(&self) -> &REGION_FILTER_EN {
        &self.region_filter_en
    }
    #[doc = "0x04..0x34 - Cluster REGION%s, containing REGION*_ADDR_START, REGION*_ADDR_END, REGION*_PMS_ATTR"]
    #[inline(always)]
    pub const fn region(&self, n: usize) -> &REGION {
        &self.region[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x04..0x34 - Cluster REGION%s, containing REGION*_ADDR_START, REGION*_ADDR_END, REGION*_PMS_ATTR"]
    #[inline(always)]
    pub fn region_iter(&self) -> impl Iterator<Item = &REGION> {
        self.region.iter()
    }
    #[doc = "0xc4 - PMS function control register"]
    #[inline(always)]
    pub const fn func_ctrl(&self) -> &FUNC_CTRL {
        &self.func_ctrl
    }
    #[doc = "0xc8..0xe8 - Cluster M%s, containing M?_STATUS, M?_STATUS_CLR, M?_EXCEPTION_INFO0, M?_EXCEPTION_INFO1"]
    #[inline(always)]
    pub const fn m(&self, n: usize) -> &M {
        &self.m[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0xc8..0xe8 - Cluster M%s, containing M?_STATUS, M?_STATUS_CLR, M?_EXCEPTION_INFO0, M?_EXCEPTION_INFO1"]
    #[inline(always)]
    pub fn m_iter(&self) -> impl Iterator<Item = &M> {
        self.m.iter()
    }
    #[doc = "0xe8 - APM interrupt enable register"]
    #[inline(always)]
    pub const fn int_en(&self) -> &INT_EN {
        &self.int_en
    }
    #[doc = "0xec - clock gating register"]
    #[inline(always)]
    pub const fn clock_gate(&self) -> &CLOCK_GATE {
        &self.clock_gate
    }
    #[doc = "0xfc - Version register"]
    #[inline(always)]
    pub const fn date(&self) -> &DATE {
        &self.date
    }
}
#[doc = "REGION_FILTER_EN (rw) register accessor: Region filter enable register\n\nYou can [`read`](crate::Reg::read) this register and get [`region_filter_en::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`region_filter_en::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@region_filter_en`] module"]
pub type REGION_FILTER_EN = crate::Reg<region_filter_en::REGION_FILTER_EN_SPEC>;
#[doc = "Region filter enable register"]
pub mod region_filter_en;
#[doc = "Cluster REGION%s, containing REGION*_ADDR_START, REGION*_ADDR_END, REGION*_PMS_ATTR"]
pub use self::region::REGION;
#[doc = r"Cluster"]
#[doc = "Cluster REGION%s, containing REGION*_ADDR_START, REGION*_ADDR_END, REGION*_PMS_ATTR"]
pub mod region;
#[doc = "FUNC_CTRL (rw) register accessor: PMS function control register\n\nYou can [`read`](crate::Reg::read) this register and get [`func_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`func_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@func_ctrl`] module"]
pub type FUNC_CTRL = crate::Reg<func_ctrl::FUNC_CTRL_SPEC>;
#[doc = "PMS function control register"]
pub mod func_ctrl;
#[doc = "Cluster M%s, containing M?_STATUS, M?_STATUS_CLR, M?_EXCEPTION_INFO0, M?_EXCEPTION_INFO1"]
pub use self::m::M;
#[doc = r"Cluster"]
#[doc = "Cluster M%s, containing M?_STATUS, M?_STATUS_CLR, M?_EXCEPTION_INFO0, M?_EXCEPTION_INFO1"]
pub mod m;
#[doc = "INT_EN (rw) register accessor: APM interrupt enable register\n\nYou can [`read`](crate::Reg::read) this register and get [`int_en::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_en::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_en`] module"]
pub type INT_EN = crate::Reg<int_en::INT_EN_SPEC>;
#[doc = "APM interrupt enable register"]
pub mod int_en;
#[doc = "CLOCK_GATE (rw) register accessor: clock gating register\n\nYou can [`read`](crate::Reg::read) this register and get [`clock_gate::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clock_gate::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@clock_gate`] module"]
pub type CLOCK_GATE = crate::Reg<clock_gate::CLOCK_GATE_SPEC>;
#[doc = "clock gating register"]
pub mod clock_gate;
pub use crate::aes::{date, DATE};
