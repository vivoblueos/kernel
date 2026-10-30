#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    _reserved0: [u8; 0x0c],
    int_raw: INT_RAW,
    int_st: INT_ST,
    int_ena: INT_ENA,
    int_clr: INT_CLR,
    _reserved4: [u8; 0x04],
    rx_conf: RX_CONF,
    tx_conf: TX_CONF,
    rx_conf1: RX_CONF1,
    tx_conf1: TX_CONF1,
    rx_clkm_conf: RX_CLKM_CONF,
    tx_clkm_conf: TX_CLKM_CONF,
    rx_clkm_div_conf: RX_CLKM_DIV_CONF,
    tx_clkm_div_conf: TX_CLKM_DIV_CONF,
    tx_pcm2pdm_conf: TX_PCM2PDM_CONF,
    tx_pcm2pdm_conf1: TX_PCM2PDM_CONF1,
    _reserved14: [u8; 0x08],
    rx_tdm_ctrl: RX_TDM_CTRL,
    tx_tdm_ctrl: TX_TDM_CTRL,
    rx_timing: RX_TIMING,
    tx_timing: TX_TIMING,
    lc_hung_conf: LC_HUNG_CONF,
    rxeof_num: RXEOF_NUM,
    conf_sigle_data: CONF_SIGLE_DATA,
    state: STATE,
    etm_conf: ETM_CONF,
    _reserved23: [u8; 0x0c],
    date: DATE,
}
impl RegisterBlock {
    #[doc = "0x0c - I2S interrupt raw register, valid in level."]
    #[inline(always)]
    pub const fn int_raw(&self) -> &INT_RAW {
        &self.int_raw
    }
    #[doc = "0x10 - I2S interrupt status register."]
    #[inline(always)]
    pub const fn int_st(&self) -> &INT_ST {
        &self.int_st
    }
    #[doc = "0x14 - I2S interrupt enable register."]
    #[inline(always)]
    pub const fn int_ena(&self) -> &INT_ENA {
        &self.int_ena
    }
    #[doc = "0x18 - I2S interrupt clear register."]
    #[inline(always)]
    pub const fn int_clr(&self) -> &INT_CLR {
        &self.int_clr
    }
    #[doc = "0x20 - I2S RX configure register"]
    #[inline(always)]
    pub const fn rx_conf(&self) -> &RX_CONF {
        &self.rx_conf
    }
    #[doc = "0x24 - I2S TX configure register"]
    #[inline(always)]
    pub const fn tx_conf(&self) -> &TX_CONF {
        &self.tx_conf
    }
    #[doc = "0x28 - I2S RX configure register 1"]
    #[inline(always)]
    pub const fn rx_conf1(&self) -> &RX_CONF1 {
        &self.rx_conf1
    }
    #[doc = "0x2c - I2S TX configure register 1"]
    #[inline(always)]
    pub const fn tx_conf1(&self) -> &TX_CONF1 {
        &self.tx_conf1
    }
    #[doc = "0x30 - I2S RX clock configure register"]
    #[inline(always)]
    pub const fn rx_clkm_conf(&self) -> &RX_CLKM_CONF {
        &self.rx_clkm_conf
    }
    #[doc = "0x34 - I2S TX clock configure register"]
    #[inline(always)]
    pub const fn tx_clkm_conf(&self) -> &TX_CLKM_CONF {
        &self.tx_clkm_conf
    }
    #[doc = "0x38 - I2S RX module clock divider configure register"]
    #[inline(always)]
    pub const fn rx_clkm_div_conf(&self) -> &RX_CLKM_DIV_CONF {
        &self.rx_clkm_div_conf
    }
    #[doc = "0x3c - I2S TX module clock divider configure register"]
    #[inline(always)]
    pub const fn tx_clkm_div_conf(&self) -> &TX_CLKM_DIV_CONF {
        &self.tx_clkm_div_conf
    }
    #[doc = "0x40 - I2S TX PCM2PDM configuration register"]
    #[inline(always)]
    pub const fn tx_pcm2pdm_conf(&self) -> &TX_PCM2PDM_CONF {
        &self.tx_pcm2pdm_conf
    }
    #[doc = "0x44 - I2S TX PCM2PDM configuration register"]
    #[inline(always)]
    pub const fn tx_pcm2pdm_conf1(&self) -> &TX_PCM2PDM_CONF1 {
        &self.tx_pcm2pdm_conf1
    }
    #[doc = "0x50 - I2S TX TDM mode control register"]
    #[inline(always)]
    pub const fn rx_tdm_ctrl(&self) -> &RX_TDM_CTRL {
        &self.rx_tdm_ctrl
    }
    #[doc = "0x54 - I2S TX TDM mode control register"]
    #[inline(always)]
    pub const fn tx_tdm_ctrl(&self) -> &TX_TDM_CTRL {
        &self.tx_tdm_ctrl
    }
    #[doc = "0x58 - I2S RX timing control register"]
    #[inline(always)]
    pub const fn rx_timing(&self) -> &RX_TIMING {
        &self.rx_timing
    }
    #[doc = "0x5c - I2S TX timing control register"]
    #[inline(always)]
    pub const fn tx_timing(&self) -> &TX_TIMING {
        &self.tx_timing
    }
    #[doc = "0x60 - I2S HUNG configure register."]
    #[inline(always)]
    pub const fn lc_hung_conf(&self) -> &LC_HUNG_CONF {
        &self.lc_hung_conf
    }
    #[doc = "0x64 - I2S RX data number control register."]
    #[inline(always)]
    pub const fn rxeof_num(&self) -> &RXEOF_NUM {
        &self.rxeof_num
    }
    #[doc = "0x68 - I2S signal data register"]
    #[inline(always)]
    pub const fn conf_sigle_data(&self) -> &CONF_SIGLE_DATA {
        &self.conf_sigle_data
    }
    #[doc = "0x6c - I2S TX status register"]
    #[inline(always)]
    pub const fn state(&self) -> &STATE {
        &self.state
    }
    #[doc = "0x70 - I2S ETM configure register"]
    #[inline(always)]
    pub const fn etm_conf(&self) -> &ETM_CONF {
        &self.etm_conf
    }
    #[doc = "0x80 - Version control register"]
    #[inline(always)]
    pub const fn date(&self) -> &DATE {
        &self.date
    }
}
#[doc = "INT_RAW (r) register accessor: I2S interrupt raw register, valid in level.\n\nYou can [`read`](crate::Reg::read) this register and get [`int_raw::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_raw`] module"]
pub type INT_RAW = crate::Reg<int_raw::INT_RAW_SPEC>;
#[doc = "I2S interrupt raw register, valid in level."]
pub mod int_raw;
#[doc = "INT_ST (r) register accessor: I2S interrupt status register.\n\nYou can [`read`](crate::Reg::read) this register and get [`int_st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_st`] module"]
pub type INT_ST = crate::Reg<int_st::INT_ST_SPEC>;
#[doc = "I2S interrupt status register."]
pub mod int_st;
#[doc = "INT_ENA (rw) register accessor: I2S interrupt enable register.\n\nYou can [`read`](crate::Reg::read) this register and get [`int_ena::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_ena::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_ena`] module"]
pub type INT_ENA = crate::Reg<int_ena::INT_ENA_SPEC>;
#[doc = "I2S interrupt enable register."]
pub mod int_ena;
#[doc = "INT_CLR (w) register accessor: I2S interrupt clear register.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_clr::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_clr`] module"]
pub type INT_CLR = crate::Reg<int_clr::INT_CLR_SPEC>;
#[doc = "I2S interrupt clear register."]
pub mod int_clr;
#[doc = "RX_CONF (rw) register accessor: I2S RX configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`rx_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rx_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rx_conf`] module"]
pub type RX_CONF = crate::Reg<rx_conf::RX_CONF_SPEC>;
#[doc = "I2S RX configure register"]
pub mod rx_conf;
#[doc = "TX_CONF (rw) register accessor: I2S TX configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tx_conf`] module"]
pub type TX_CONF = crate::Reg<tx_conf::TX_CONF_SPEC>;
#[doc = "I2S TX configure register"]
pub mod tx_conf;
#[doc = "RX_CONF1 (rw) register accessor: I2S RX configure register 1\n\nYou can [`read`](crate::Reg::read) this register and get [`rx_conf1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rx_conf1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rx_conf1`] module"]
pub type RX_CONF1 = crate::Reg<rx_conf1::RX_CONF1_SPEC>;
#[doc = "I2S RX configure register 1"]
pub mod rx_conf1;
#[doc = "TX_CONF1 (rw) register accessor: I2S TX configure register 1\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_conf1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_conf1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tx_conf1`] module"]
pub type TX_CONF1 = crate::Reg<tx_conf1::TX_CONF1_SPEC>;
#[doc = "I2S TX configure register 1"]
pub mod tx_conf1;
#[doc = "RX_CLKM_CONF (rw) register accessor: I2S RX clock configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`rx_clkm_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rx_clkm_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rx_clkm_conf`] module"]
pub type RX_CLKM_CONF = crate::Reg<rx_clkm_conf::RX_CLKM_CONF_SPEC>;
#[doc = "I2S RX clock configure register"]
pub mod rx_clkm_conf;
#[doc = "TX_CLKM_CONF (rw) register accessor: I2S TX clock configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_clkm_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_clkm_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tx_clkm_conf`] module"]
pub type TX_CLKM_CONF = crate::Reg<tx_clkm_conf::TX_CLKM_CONF_SPEC>;
#[doc = "I2S TX clock configure register"]
pub mod tx_clkm_conf;
#[doc = "RX_CLKM_DIV_CONF (rw) register accessor: I2S RX module clock divider configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`rx_clkm_div_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rx_clkm_div_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rx_clkm_div_conf`] module"]
pub type RX_CLKM_DIV_CONF = crate::Reg<rx_clkm_div_conf::RX_CLKM_DIV_CONF_SPEC>;
#[doc = "I2S RX module clock divider configure register"]
pub mod rx_clkm_div_conf;
#[doc = "TX_CLKM_DIV_CONF (rw) register accessor: I2S TX module clock divider configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_clkm_div_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_clkm_div_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tx_clkm_div_conf`] module"]
pub type TX_CLKM_DIV_CONF = crate::Reg<tx_clkm_div_conf::TX_CLKM_DIV_CONF_SPEC>;
#[doc = "I2S TX module clock divider configure register"]
pub mod tx_clkm_div_conf;
#[doc = "TX_PCM2PDM_CONF (rw) register accessor: I2S TX PCM2PDM configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_pcm2pdm_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_pcm2pdm_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tx_pcm2pdm_conf`] module"]
pub type TX_PCM2PDM_CONF = crate::Reg<tx_pcm2pdm_conf::TX_PCM2PDM_CONF_SPEC>;
#[doc = "I2S TX PCM2PDM configuration register"]
pub mod tx_pcm2pdm_conf;
#[doc = "TX_PCM2PDM_CONF1 (rw) register accessor: I2S TX PCM2PDM configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_pcm2pdm_conf1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_pcm2pdm_conf1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tx_pcm2pdm_conf1`] module"]
pub type TX_PCM2PDM_CONF1 = crate::Reg<tx_pcm2pdm_conf1::TX_PCM2PDM_CONF1_SPEC>;
#[doc = "I2S TX PCM2PDM configuration register"]
pub mod tx_pcm2pdm_conf1;
#[doc = "RX_TDM_CTRL (rw) register accessor: I2S TX TDM mode control register\n\nYou can [`read`](crate::Reg::read) this register and get [`rx_tdm_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rx_tdm_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rx_tdm_ctrl`] module"]
pub type RX_TDM_CTRL = crate::Reg<rx_tdm_ctrl::RX_TDM_CTRL_SPEC>;
#[doc = "I2S TX TDM mode control register"]
pub mod rx_tdm_ctrl;
#[doc = "TX_TDM_CTRL (rw) register accessor: I2S TX TDM mode control register\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_tdm_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_tdm_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tx_tdm_ctrl`] module"]
pub type TX_TDM_CTRL = crate::Reg<tx_tdm_ctrl::TX_TDM_CTRL_SPEC>;
#[doc = "I2S TX TDM mode control register"]
pub mod tx_tdm_ctrl;
#[doc = "RX_TIMING (rw) register accessor: I2S RX timing control register\n\nYou can [`read`](crate::Reg::read) this register and get [`rx_timing::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rx_timing::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rx_timing`] module"]
pub type RX_TIMING = crate::Reg<rx_timing::RX_TIMING_SPEC>;
#[doc = "I2S RX timing control register"]
pub mod rx_timing;
#[doc = "TX_TIMING (rw) register accessor: I2S TX timing control register\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_timing::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_timing::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tx_timing`] module"]
pub type TX_TIMING = crate::Reg<tx_timing::TX_TIMING_SPEC>;
#[doc = "I2S TX timing control register"]
pub mod tx_timing;
#[doc = "LC_HUNG_CONF (rw) register accessor: I2S HUNG configure register.\n\nYou can [`read`](crate::Reg::read) this register and get [`lc_hung_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`lc_hung_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@lc_hung_conf`] module"]
pub type LC_HUNG_CONF = crate::Reg<lc_hung_conf::LC_HUNG_CONF_SPEC>;
#[doc = "I2S HUNG configure register."]
pub mod lc_hung_conf;
#[doc = "RXEOF_NUM (rw) register accessor: I2S RX data number control register.\n\nYou can [`read`](crate::Reg::read) this register and get [`rxeof_num::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rxeof_num::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rxeof_num`] module"]
pub type RXEOF_NUM = crate::Reg<rxeof_num::RXEOF_NUM_SPEC>;
#[doc = "I2S RX data number control register."]
pub mod rxeof_num;
#[doc = "CONF_SIGLE_DATA (rw) register accessor: I2S signal data register\n\nYou can [`read`](crate::Reg::read) this register and get [`conf_sigle_data::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf_sigle_data::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@conf_sigle_data`] module"]
pub type CONF_SIGLE_DATA = crate::Reg<conf_sigle_data::CONF_SIGLE_DATA_SPEC>;
#[doc = "I2S signal data register"]
pub mod conf_sigle_data;
#[doc = "STATE (r) register accessor: I2S TX status register\n\nYou can [`read`](crate::Reg::read) this register and get [`state::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@state`] module"]
pub type STATE = crate::Reg<state::STATE_SPEC>;
#[doc = "I2S TX status register"]
pub mod state;
#[doc = "ETM_CONF (rw) register accessor: I2S ETM configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`etm_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`etm_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@etm_conf`] module"]
pub type ETM_CONF = crate::Reg<etm_conf::ETM_CONF_SPEC>;
#[doc = "I2S ETM configure register"]
pub mod etm_conf;
pub use crate::aes::{date, DATE};
