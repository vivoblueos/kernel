#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    ctrl: CTRL,
    ctrl2: CTRL2,
    filter_ctrl1: FILTER_CTRL1,
    fsm_wait: FSM_WAIT,
    sar1_status: SAR1_STATUS,
    sar2_status: SAR2_STATUS,
    sar_patt_tab1: SAR_PATT_TAB1,
    sar_patt_tab2: SAR_PATT_TAB2,
    onetime_sample: ONETIME_SAMPLE,
    arb_ctrl: ARB_CTRL,
    filter_ctrl0: FILTER_CTRL0,
    sar1data_status: SAR1DATA_STATUS,
    sar2data_status: SAR2DATA_STATUS,
    thres0_ctrl: THRES0_CTRL,
    thres1_ctrl: THRES1_CTRL,
    thres_ctrl: THRES_CTRL,
    int_ena: INT_ENA,
    int_raw: INT_RAW,
    int_st: INT_ST,
    int_clr: INT_CLR,
    dma_conf: DMA_CONF,
    clkm_conf: CLKM_CONF,
    tsens_ctrl: TSENS_CTRL,
    tsens_ctrl2: TSENS_CTRL2,
    cali: CALI,
    _reserved25: [u8; 0x0398],
    ctrl_date: CTRL_DATE,
}
impl RegisterBlock {
    #[doc = "0x00 - digital saradc configure register"]
    #[inline(always)]
    pub const fn ctrl(&self) -> &CTRL {
        &self.ctrl
    }
    #[doc = "0x04 - digital saradc configure register"]
    #[inline(always)]
    pub const fn ctrl2(&self) -> &CTRL2 {
        &self.ctrl2
    }
    #[doc = "0x08 - digital saradc configure register"]
    #[inline(always)]
    pub const fn filter_ctrl1(&self) -> &FILTER_CTRL1 {
        &self.filter_ctrl1
    }
    #[doc = "0x0c - digital saradc configure register"]
    #[inline(always)]
    pub const fn fsm_wait(&self) -> &FSM_WAIT {
        &self.fsm_wait
    }
    #[doc = "0x10 - digital saradc configure register"]
    #[inline(always)]
    pub const fn sar1_status(&self) -> &SAR1_STATUS {
        &self.sar1_status
    }
    #[doc = "0x14 - digital saradc configure register"]
    #[inline(always)]
    pub const fn sar2_status(&self) -> &SAR2_STATUS {
        &self.sar2_status
    }
    #[doc = "0x18 - digital saradc configure register"]
    #[inline(always)]
    pub const fn sar_patt_tab1(&self) -> &SAR_PATT_TAB1 {
        &self.sar_patt_tab1
    }
    #[doc = "0x1c - digital saradc configure register"]
    #[inline(always)]
    pub const fn sar_patt_tab2(&self) -> &SAR_PATT_TAB2 {
        &self.sar_patt_tab2
    }
    #[doc = "0x20 - digital saradc configure register"]
    #[inline(always)]
    pub const fn onetime_sample(&self) -> &ONETIME_SAMPLE {
        &self.onetime_sample
    }
    #[doc = "0x24 - digital saradc configure register"]
    #[inline(always)]
    pub const fn arb_ctrl(&self) -> &ARB_CTRL {
        &self.arb_ctrl
    }
    #[doc = "0x28 - digital saradc configure register"]
    #[inline(always)]
    pub const fn filter_ctrl0(&self) -> &FILTER_CTRL0 {
        &self.filter_ctrl0
    }
    #[doc = "0x2c - digital saradc configure register"]
    #[inline(always)]
    pub const fn sar1data_status(&self) -> &SAR1DATA_STATUS {
        &self.sar1data_status
    }
    #[doc = "0x30 - digital saradc configure register"]
    #[inline(always)]
    pub const fn sar2data_status(&self) -> &SAR2DATA_STATUS {
        &self.sar2data_status
    }
    #[doc = "0x34 - digital saradc configure register"]
    #[inline(always)]
    pub const fn thres0_ctrl(&self) -> &THRES0_CTRL {
        &self.thres0_ctrl
    }
    #[doc = "0x38 - digital saradc configure register"]
    #[inline(always)]
    pub const fn thres1_ctrl(&self) -> &THRES1_CTRL {
        &self.thres1_ctrl
    }
    #[doc = "0x3c - digital saradc configure register"]
    #[inline(always)]
    pub const fn thres_ctrl(&self) -> &THRES_CTRL {
        &self.thres_ctrl
    }
    #[doc = "0x40 - digital saradc int register"]
    #[inline(always)]
    pub const fn int_ena(&self) -> &INT_ENA {
        &self.int_ena
    }
    #[doc = "0x44 - digital saradc int register"]
    #[inline(always)]
    pub const fn int_raw(&self) -> &INT_RAW {
        &self.int_raw
    }
    #[doc = "0x48 - digital saradc int register"]
    #[inline(always)]
    pub const fn int_st(&self) -> &INT_ST {
        &self.int_st
    }
    #[doc = "0x4c - digital saradc int register"]
    #[inline(always)]
    pub const fn int_clr(&self) -> &INT_CLR {
        &self.int_clr
    }
    #[doc = "0x50 - digital saradc configure register"]
    #[inline(always)]
    pub const fn dma_conf(&self) -> &DMA_CONF {
        &self.dma_conf
    }
    #[doc = "0x54 - digital saradc configure register"]
    #[inline(always)]
    pub const fn clkm_conf(&self) -> &CLKM_CONF {
        &self.clkm_conf
    }
    #[doc = "0x58 - digital tsens configure register"]
    #[inline(always)]
    pub const fn tsens_ctrl(&self) -> &TSENS_CTRL {
        &self.tsens_ctrl
    }
    #[doc = "0x5c - digital tsens configure register"]
    #[inline(always)]
    pub const fn tsens_ctrl2(&self) -> &TSENS_CTRL2 {
        &self.tsens_ctrl2
    }
    #[doc = "0x60 - digital saradc configure register"]
    #[inline(always)]
    pub const fn cali(&self) -> &CALI {
        &self.cali
    }
    #[doc = "0x3fc - version"]
    #[inline(always)]
    pub const fn ctrl_date(&self) -> &CTRL_DATE {
        &self.ctrl_date
    }
}
#[doc = "CTRL (rw) register accessor: digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ctrl`] module"]
pub type CTRL = crate::Reg<ctrl::CTRL_SPEC>;
#[doc = "digital saradc configure register"]
pub mod ctrl;
#[doc = "CTRL2 (rw) register accessor: digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`ctrl2::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ctrl2::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ctrl2`] module"]
pub type CTRL2 = crate::Reg<ctrl2::CTRL2_SPEC>;
#[doc = "digital saradc configure register"]
pub mod ctrl2;
#[doc = "FILTER_CTRL1 (rw) register accessor: digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`filter_ctrl1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`filter_ctrl1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@filter_ctrl1`] module"]
pub type FILTER_CTRL1 = crate::Reg<filter_ctrl1::FILTER_CTRL1_SPEC>;
#[doc = "digital saradc configure register"]
pub mod filter_ctrl1;
#[doc = "FSM_WAIT (rw) register accessor: digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`fsm_wait::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`fsm_wait::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@fsm_wait`] module"]
pub type FSM_WAIT = crate::Reg<fsm_wait::FSM_WAIT_SPEC>;
#[doc = "digital saradc configure register"]
pub mod fsm_wait;
#[doc = "SAR1_STATUS (r) register accessor: digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`sar1_status::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sar1_status`] module"]
pub type SAR1_STATUS = crate::Reg<sar1_status::SAR1_STATUS_SPEC>;
#[doc = "digital saradc configure register"]
pub mod sar1_status;
#[doc = "SAR2_STATUS (r) register accessor: digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`sar2_status::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sar2_status`] module"]
pub type SAR2_STATUS = crate::Reg<sar2_status::SAR2_STATUS_SPEC>;
#[doc = "digital saradc configure register"]
pub mod sar2_status;
#[doc = "SAR_PATT_TAB1 (rw) register accessor: digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`sar_patt_tab1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sar_patt_tab1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sar_patt_tab1`] module"]
pub type SAR_PATT_TAB1 = crate::Reg<sar_patt_tab1::SAR_PATT_TAB1_SPEC>;
#[doc = "digital saradc configure register"]
pub mod sar_patt_tab1;
#[doc = "SAR_PATT_TAB2 (rw) register accessor: digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`sar_patt_tab2::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sar_patt_tab2::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sar_patt_tab2`] module"]
pub type SAR_PATT_TAB2 = crate::Reg<sar_patt_tab2::SAR_PATT_TAB2_SPEC>;
#[doc = "digital saradc configure register"]
pub mod sar_patt_tab2;
#[doc = "ONETIME_SAMPLE (rw) register accessor: digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`onetime_sample::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`onetime_sample::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@onetime_sample`] module"]
pub type ONETIME_SAMPLE = crate::Reg<onetime_sample::ONETIME_SAMPLE_SPEC>;
#[doc = "digital saradc configure register"]
pub mod onetime_sample;
#[doc = "ARB_CTRL (rw) register accessor: digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`arb_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`arb_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@arb_ctrl`] module"]
pub type ARB_CTRL = crate::Reg<arb_ctrl::ARB_CTRL_SPEC>;
#[doc = "digital saradc configure register"]
pub mod arb_ctrl;
#[doc = "FILTER_CTRL0 (rw) register accessor: digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`filter_ctrl0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`filter_ctrl0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@filter_ctrl0`] module"]
pub type FILTER_CTRL0 = crate::Reg<filter_ctrl0::FILTER_CTRL0_SPEC>;
#[doc = "digital saradc configure register"]
pub mod filter_ctrl0;
#[doc = "SAR1DATA_STATUS (r) register accessor: digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`sar1data_status::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sar1data_status`] module"]
pub type SAR1DATA_STATUS = crate::Reg<sar1data_status::SAR1DATA_STATUS_SPEC>;
#[doc = "digital saradc configure register"]
pub mod sar1data_status;
#[doc = "SAR2DATA_STATUS (r) register accessor: digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`sar2data_status::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sar2data_status`] module"]
pub type SAR2DATA_STATUS = crate::Reg<sar2data_status::SAR2DATA_STATUS_SPEC>;
#[doc = "digital saradc configure register"]
pub mod sar2data_status;
#[doc = "THRES0_CTRL (rw) register accessor: digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`thres0_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`thres0_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@thres0_ctrl`] module"]
pub type THRES0_CTRL = crate::Reg<thres0_ctrl::THRES0_CTRL_SPEC>;
#[doc = "digital saradc configure register"]
pub mod thres0_ctrl;
#[doc = "THRES1_CTRL (rw) register accessor: digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`thres1_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`thres1_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@thres1_ctrl`] module"]
pub type THRES1_CTRL = crate::Reg<thres1_ctrl::THRES1_CTRL_SPEC>;
#[doc = "digital saradc configure register"]
pub mod thres1_ctrl;
#[doc = "THRES_CTRL (rw) register accessor: digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`thres_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`thres_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@thres_ctrl`] module"]
pub type THRES_CTRL = crate::Reg<thres_ctrl::THRES_CTRL_SPEC>;
#[doc = "digital saradc configure register"]
pub mod thres_ctrl;
#[doc = "INT_ENA (rw) register accessor: digital saradc int register\n\nYou can [`read`](crate::Reg::read) this register and get [`int_ena::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_ena::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_ena`] module"]
pub type INT_ENA = crate::Reg<int_ena::INT_ENA_SPEC>;
#[doc = "digital saradc int register"]
pub mod int_ena;
#[doc = "INT_RAW (r) register accessor: digital saradc int register\n\nYou can [`read`](crate::Reg::read) this register and get [`int_raw::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_raw`] module"]
pub type INT_RAW = crate::Reg<int_raw::INT_RAW_SPEC>;
#[doc = "digital saradc int register"]
pub mod int_raw;
#[doc = "INT_ST (r) register accessor: digital saradc int register\n\nYou can [`read`](crate::Reg::read) this register and get [`int_st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_st`] module"]
pub type INT_ST = crate::Reg<int_st::INT_ST_SPEC>;
#[doc = "digital saradc int register"]
pub mod int_st;
#[doc = "INT_CLR (w) register accessor: digital saradc int register\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_clr::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_clr`] module"]
pub type INT_CLR = crate::Reg<int_clr::INT_CLR_SPEC>;
#[doc = "digital saradc int register"]
pub mod int_clr;
#[doc = "DMA_CONF (rw) register accessor: digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`dma_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dma_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dma_conf`] module"]
pub type DMA_CONF = crate::Reg<dma_conf::DMA_CONF_SPEC>;
#[doc = "digital saradc configure register"]
pub mod dma_conf;
#[doc = "CLKM_CONF (rw) register accessor: digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`clkm_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clkm_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@clkm_conf`] module"]
pub type CLKM_CONF = crate::Reg<clkm_conf::CLKM_CONF_SPEC>;
#[doc = "digital saradc configure register"]
pub mod clkm_conf;
#[doc = "TSENS_CTRL (rw) register accessor: digital tsens configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`tsens_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tsens_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tsens_ctrl`] module"]
pub type TSENS_CTRL = crate::Reg<tsens_ctrl::TSENS_CTRL_SPEC>;
#[doc = "digital tsens configure register"]
pub mod tsens_ctrl;
#[doc = "TSENS_CTRL2 (rw) register accessor: digital tsens configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`tsens_ctrl2::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tsens_ctrl2::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tsens_ctrl2`] module"]
pub type TSENS_CTRL2 = crate::Reg<tsens_ctrl2::TSENS_CTRL2_SPEC>;
#[doc = "digital tsens configure register"]
pub mod tsens_ctrl2;
#[doc = "CALI (rw) register accessor: digital saradc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`cali::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cali::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cali`] module"]
pub type CALI = crate::Reg<cali::CALI_SPEC>;
#[doc = "digital saradc configure register"]
pub mod cali;
pub use crate::aes::{date as ctrl_date, DATE as CTRL_DATE};
