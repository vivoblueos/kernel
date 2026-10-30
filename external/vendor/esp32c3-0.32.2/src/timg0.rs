#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    t: [T; 1],
    _reserved1: [u8; 0x24],
    wdtconfig0: WDTCONFIG0,
    wdtconfig1: WDTCONFIG1,
    wdtconfig: [WDTCONFIG; 4],
    wdtfeed: WDTFEED,
    wdtwprotect: WDTWPROTECT,
    rtccalicfg: RTCCALICFG,
    rtccalicfg1: RTCCALICFG1,
    int_ena: INT_ENA,
    int_raw: INT_RAW,
    int_st: INT_ST,
    int_clr: INT_CLR,
    rtccalicfg2: RTCCALICFG2,
    _reserved13: [u8; 0x74],
    ntimg_date: NTIMG_DATE,
    regclk: REGCLK,
}
impl RegisterBlock {
    #[doc = "0x00..0x24 - Cluster T%s, containing T?CONFIG, T?LO, T?HI, T?UPDATE, T?ALARMLO, T?ALARMHI, T?LOADLO, T?LOADHI, T?LOAD"]
    #[inline(always)]
    pub const fn t(&self, n: usize) -> &T {
        &self.t[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x00..0x24 - Cluster T%s, containing T?CONFIG, T?LO, T?HI, T?UPDATE, T?ALARMLO, T?ALARMHI, T?LOADLO, T?LOADHI, T?LOAD"]
    #[inline(always)]
    pub fn t_iter(&self) -> impl Iterator<Item = &T> {
        self.t.iter()
    }
    #[doc = "0x48 - TIMG_WDTCONFIG0_REG."]
    #[inline(always)]
    pub const fn wdtconfig0(&self) -> &WDTCONFIG0 {
        &self.wdtconfig0
    }
    #[doc = "0x4c - TIMG_WDTCONFIG1_REG."]
    #[inline(always)]
    pub const fn wdtconfig1(&self) -> &WDTCONFIG1 {
        &self.wdtconfig1
    }
    #[doc = "0x50..0x60 - Watchdog timer stage timeout value"]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is the index of register in the array. `n == 0` corresponds to `WDTCONFIG2` register.</div>"]
    #[inline(always)]
    pub const fn wdtconfig(&self, n: usize) -> &WDTCONFIG {
        &self.wdtconfig[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x50..0x60 - Watchdog timer stage timeout value"]
    #[inline(always)]
    pub fn wdtconfig_iter(&self) -> impl Iterator<Item = &WDTCONFIG> {
        self.wdtconfig.iter()
    }
    #[doc = "0x50 - Watchdog timer stage timeout value"]
    #[inline(always)]
    pub const fn wdtconfig2(&self) -> &WDTCONFIG {
        self.wdtconfig(0)
    }
    #[doc = "0x54 - Watchdog timer stage timeout value"]
    #[inline(always)]
    pub const fn wdtconfig3(&self) -> &WDTCONFIG {
        self.wdtconfig(1)
    }
    #[doc = "0x58 - Watchdog timer stage timeout value"]
    #[inline(always)]
    pub const fn wdtconfig4(&self) -> &WDTCONFIG {
        self.wdtconfig(2)
    }
    #[doc = "0x5c - Watchdog timer stage timeout value"]
    #[inline(always)]
    pub const fn wdtconfig5(&self) -> &WDTCONFIG {
        self.wdtconfig(3)
    }
    #[doc = "0x60 - TIMG_WDTFEED_REG."]
    #[inline(always)]
    pub const fn wdtfeed(&self) -> &WDTFEED {
        &self.wdtfeed
    }
    #[doc = "0x64 - TIMG_WDTWPROTECT_REG."]
    #[inline(always)]
    pub const fn wdtwprotect(&self) -> &WDTWPROTECT {
        &self.wdtwprotect
    }
    #[doc = "0x68 - TIMG_RTCCALICFG_REG."]
    #[inline(always)]
    pub const fn rtccalicfg(&self) -> &RTCCALICFG {
        &self.rtccalicfg
    }
    #[doc = "0x6c - TIMG_RTCCALICFG1_REG."]
    #[inline(always)]
    pub const fn rtccalicfg1(&self) -> &RTCCALICFG1 {
        &self.rtccalicfg1
    }
    #[doc = "0x70 - INT_ENA_TIMG_REG"]
    #[inline(always)]
    pub const fn int_ena(&self) -> &INT_ENA {
        &self.int_ena
    }
    #[doc = "0x74 - INT_RAW_TIMG_REG"]
    #[inline(always)]
    pub const fn int_raw(&self) -> &INT_RAW {
        &self.int_raw
    }
    #[doc = "0x78 - INT_ST_TIMG_REG"]
    #[inline(always)]
    pub const fn int_st(&self) -> &INT_ST {
        &self.int_st
    }
    #[doc = "0x7c - INT_CLR_TIMG_REG"]
    #[inline(always)]
    pub const fn int_clr(&self) -> &INT_CLR {
        &self.int_clr
    }
    #[doc = "0x80 - TIMG_RTCCALICFG2_REG."]
    #[inline(always)]
    pub const fn rtccalicfg2(&self) -> &RTCCALICFG2 {
        &self.rtccalicfg2
    }
    #[doc = "0xf8 - TIMG_NTIMG_DATE_REG."]
    #[inline(always)]
    pub const fn ntimg_date(&self) -> &NTIMG_DATE {
        &self.ntimg_date
    }
    #[doc = "0xfc - TIMG_REGCLK_REG."]
    #[inline(always)]
    pub const fn regclk(&self) -> &REGCLK {
        &self.regclk
    }
}
#[doc = "Cluster T%s, containing T?CONFIG, T?LO, T?HI, T?UPDATE, T?ALARMLO, T?ALARMHI, T?LOADLO, T?LOADHI, T?LOAD"]
pub use self::t::T;
#[doc = r"Cluster"]
#[doc = "Cluster T%s, containing T?CONFIG, T?LO, T?HI, T?UPDATE, T?ALARMLO, T?ALARMHI, T?LOADLO, T?LOADHI, T?LOAD"]
pub mod t;
#[doc = "WDTCONFIG0 (rw) register accessor: TIMG_WDTCONFIG0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`wdtconfig0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`wdtconfig0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@wdtconfig0`] module"]
pub type WDTCONFIG0 = crate::Reg<wdtconfig0::WDTCONFIG0_SPEC>;
#[doc = "TIMG_WDTCONFIG0_REG."]
pub mod wdtconfig0;
#[doc = "WDTCONFIG1 (rw) register accessor: TIMG_WDTCONFIG1_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`wdtconfig1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`wdtconfig1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@wdtconfig1`] module"]
pub type WDTCONFIG1 = crate::Reg<wdtconfig1::WDTCONFIG1_SPEC>;
#[doc = "TIMG_WDTCONFIG1_REG."]
pub mod wdtconfig1;
#[doc = "WDTCONFIG (rw) register accessor: Watchdog timer stage timeout value\n\nYou can [`read`](crate::Reg::read) this register and get [`wdtconfig::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`wdtconfig::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@wdtconfig`] module"]
pub type WDTCONFIG = crate::Reg<wdtconfig::WDTCONFIG_SPEC>;
#[doc = "Watchdog timer stage timeout value"]
pub mod wdtconfig;
#[doc = "WDTFEED (w) register accessor: TIMG_WDTFEED_REG.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`wdtfeed::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@wdtfeed`] module"]
pub type WDTFEED = crate::Reg<wdtfeed::WDTFEED_SPEC>;
#[doc = "TIMG_WDTFEED_REG."]
pub mod wdtfeed;
#[doc = "WDTWPROTECT (rw) register accessor: TIMG_WDTWPROTECT_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`wdtwprotect::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`wdtwprotect::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@wdtwprotect`] module"]
pub type WDTWPROTECT = crate::Reg<wdtwprotect::WDTWPROTECT_SPEC>;
#[doc = "TIMG_WDTWPROTECT_REG."]
pub mod wdtwprotect;
#[doc = "RTCCALICFG (rw) register accessor: TIMG_RTCCALICFG_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`rtccalicfg::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rtccalicfg::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rtccalicfg`] module"]
pub type RTCCALICFG = crate::Reg<rtccalicfg::RTCCALICFG_SPEC>;
#[doc = "TIMG_RTCCALICFG_REG."]
pub mod rtccalicfg;
#[doc = "RTCCALICFG1 (r) register accessor: TIMG_RTCCALICFG1_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`rtccalicfg1::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rtccalicfg1`] module"]
pub type RTCCALICFG1 = crate::Reg<rtccalicfg1::RTCCALICFG1_SPEC>;
#[doc = "TIMG_RTCCALICFG1_REG."]
pub mod rtccalicfg1;
#[doc = "INT_ENA (rw) register accessor: INT_ENA_TIMG_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`int_ena::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_ena::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_ena`] module"]
pub type INT_ENA = crate::Reg<int_ena::INT_ENA_SPEC>;
#[doc = "INT_ENA_TIMG_REG"]
pub mod int_ena;
#[doc = "INT_RAW (r) register accessor: INT_RAW_TIMG_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`int_raw::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_raw`] module"]
pub type INT_RAW = crate::Reg<int_raw::INT_RAW_SPEC>;
#[doc = "INT_RAW_TIMG_REG"]
pub mod int_raw;
#[doc = "INT_ST (r) register accessor: INT_ST_TIMG_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`int_st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_st`] module"]
pub type INT_ST = crate::Reg<int_st::INT_ST_SPEC>;
#[doc = "INT_ST_TIMG_REG"]
pub mod int_st;
#[doc = "INT_CLR (w) register accessor: INT_CLR_TIMG_REG\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_clr::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_clr`] module"]
pub type INT_CLR = crate::Reg<int_clr::INT_CLR_SPEC>;
#[doc = "INT_CLR_TIMG_REG"]
pub mod int_clr;
#[doc = "RTCCALICFG2 (rw) register accessor: TIMG_RTCCALICFG2_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`rtccalicfg2::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rtccalicfg2::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rtccalicfg2`] module"]
pub type RTCCALICFG2 = crate::Reg<rtccalicfg2::RTCCALICFG2_SPEC>;
#[doc = "TIMG_RTCCALICFG2_REG."]
pub mod rtccalicfg2;
pub use crate::aes::{date as ntimg_date, DATE as NTIMG_DATE};
#[doc = "REGCLK (rw) register accessor: TIMG_REGCLK_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`regclk::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`regclk::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@regclk`] module"]
pub type REGCLK = crate::Reg<regclk::REGCLK_SPEC>;
#[doc = "TIMG_REGCLK_REG."]
pub mod regclk;
