#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    log_setting: LOG_SETTING,
    log_check_data: LOG_CHECK_DATA,
    log_data_mask: LOG_DATA_MASK,
    log_min: LOG_MIN,
    log_max: LOG_MAX,
    log_mem_start: LOG_MEM_START,
    log_mem_end: LOG_MEM_END,
    log_mem_current_addr: LOG_MEM_CURRENT_ADDR,
    log_mem_addr_update: LOG_MEM_ADDR_UPDATE,
    log_mem_full_flag: LOG_MEM_FULL_FLAG,
    clock_gate: CLOCK_GATE,
    _reserved11: [u8; 0x03d0],
    date: DATE,
}
impl RegisterBlock {
    #[doc = "0x00 - log config regsiter"]
    #[inline(always)]
    pub const fn log_setting(&self) -> &LOG_SETTING {
        &self.log_setting
    }
    #[doc = "0x04 - check data regsiter"]
    #[inline(always)]
    pub const fn log_check_data(&self) -> &LOG_CHECK_DATA {
        &self.log_check_data
    }
    #[doc = "0x08 - check data mask register"]
    #[inline(always)]
    pub const fn log_data_mask(&self) -> &LOG_DATA_MASK {
        &self.log_data_mask
    }
    #[doc = "0x0c - log boundary regsiter"]
    #[inline(always)]
    pub const fn log_min(&self) -> &LOG_MIN {
        &self.log_min
    }
    #[doc = "0x10 - log boundary regsiter"]
    #[inline(always)]
    pub const fn log_max(&self) -> &LOG_MAX {
        &self.log_max
    }
    #[doc = "0x14 - log message store range register"]
    #[inline(always)]
    pub const fn log_mem_start(&self) -> &LOG_MEM_START {
        &self.log_mem_start
    }
    #[doc = "0x18 - log message store range register"]
    #[inline(always)]
    pub const fn log_mem_end(&self) -> &LOG_MEM_END {
        &self.log_mem_end
    }
    #[doc = "0x1c - current writing address."]
    #[inline(always)]
    pub const fn log_mem_current_addr(&self) -> &LOG_MEM_CURRENT_ADDR {
        &self.log_mem_current_addr
    }
    #[doc = "0x20 - writing address update"]
    #[inline(always)]
    pub const fn log_mem_addr_update(&self) -> &LOG_MEM_ADDR_UPDATE {
        &self.log_mem_addr_update
    }
    #[doc = "0x24 - full flag status register"]
    #[inline(always)]
    pub const fn log_mem_full_flag(&self) -> &LOG_MEM_FULL_FLAG {
        &self.log_mem_full_flag
    }
    #[doc = "0x28 - clock gate force on register"]
    #[inline(always)]
    pub const fn clock_gate(&self) -> &CLOCK_GATE {
        &self.clock_gate
    }
    #[doc = "0x3fc - version register"]
    #[inline(always)]
    pub const fn date(&self) -> &DATE {
        &self.date
    }
}
#[doc = "LOG_SETTING (rw) register accessor: log config regsiter\n\nYou can [`read`](crate::Reg::read) this register and get [`log_setting::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`log_setting::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@log_setting`] module"]
pub type LOG_SETTING = crate::Reg<log_setting::LOG_SETTING_SPEC>;
#[doc = "log config regsiter"]
pub mod log_setting;
#[doc = "LOG_CHECK_DATA (rw) register accessor: check data regsiter\n\nYou can [`read`](crate::Reg::read) this register and get [`log_check_data::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`log_check_data::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@log_check_data`] module"]
pub type LOG_CHECK_DATA = crate::Reg<log_check_data::LOG_CHECK_DATA_SPEC>;
#[doc = "check data regsiter"]
pub mod log_check_data;
#[doc = "LOG_DATA_MASK (rw) register accessor: check data mask register\n\nYou can [`read`](crate::Reg::read) this register and get [`log_data_mask::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`log_data_mask::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@log_data_mask`] module"]
pub type LOG_DATA_MASK = crate::Reg<log_data_mask::LOG_DATA_MASK_SPEC>;
#[doc = "check data mask register"]
pub mod log_data_mask;
#[doc = "LOG_MIN (rw) register accessor: log boundary regsiter\n\nYou can [`read`](crate::Reg::read) this register and get [`log_min::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`log_min::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@log_min`] module"]
pub type LOG_MIN = crate::Reg<log_min::LOG_MIN_SPEC>;
#[doc = "log boundary regsiter"]
pub mod log_min;
#[doc = "LOG_MAX (rw) register accessor: log boundary regsiter\n\nYou can [`read`](crate::Reg::read) this register and get [`log_max::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`log_max::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@log_max`] module"]
pub type LOG_MAX = crate::Reg<log_max::LOG_MAX_SPEC>;
#[doc = "log boundary regsiter"]
pub mod log_max;
#[doc = "LOG_MEM_START (rw) register accessor: log message store range register\n\nYou can [`read`](crate::Reg::read) this register and get [`log_mem_start::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`log_mem_start::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@log_mem_start`] module"]
pub type LOG_MEM_START = crate::Reg<log_mem_start::LOG_MEM_START_SPEC>;
#[doc = "log message store range register"]
pub mod log_mem_start;
#[doc = "LOG_MEM_END (rw) register accessor: log message store range register\n\nYou can [`read`](crate::Reg::read) this register and get [`log_mem_end::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`log_mem_end::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@log_mem_end`] module"]
pub type LOG_MEM_END = crate::Reg<log_mem_end::LOG_MEM_END_SPEC>;
#[doc = "log message store range register"]
pub mod log_mem_end;
#[doc = "LOG_MEM_CURRENT_ADDR (r) register accessor: current writing address.\n\nYou can [`read`](crate::Reg::read) this register and get [`log_mem_current_addr::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@log_mem_current_addr`] module"]
pub type LOG_MEM_CURRENT_ADDR = crate::Reg<log_mem_current_addr::LOG_MEM_CURRENT_ADDR_SPEC>;
#[doc = "current writing address."]
pub mod log_mem_current_addr;
#[doc = "LOG_MEM_ADDR_UPDATE (w) register accessor: writing address update\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`log_mem_addr_update::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@log_mem_addr_update`] module"]
pub type LOG_MEM_ADDR_UPDATE = crate::Reg<log_mem_addr_update::LOG_MEM_ADDR_UPDATE_SPEC>;
#[doc = "writing address update"]
pub mod log_mem_addr_update;
#[doc = "LOG_MEM_FULL_FLAG (rw) register accessor: full flag status register\n\nYou can [`read`](crate::Reg::read) this register and get [`log_mem_full_flag::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`log_mem_full_flag::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@log_mem_full_flag`] module"]
pub type LOG_MEM_FULL_FLAG = crate::Reg<log_mem_full_flag::LOG_MEM_FULL_FLAG_SPEC>;
#[doc = "full flag status register"]
pub mod log_mem_full_flag;
#[doc = "CLOCK_GATE (rw) register accessor: clock gate force on register\n\nYou can [`read`](crate::Reg::read) this register and get [`clock_gate::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clock_gate::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@clock_gate`] module"]
pub type CLOCK_GATE = crate::Reg<clock_gate::CLOCK_GATE_SPEC>;
#[doc = "clock gate force on register"]
pub mod clock_gate;
pub use crate::aes::{date, DATE};
