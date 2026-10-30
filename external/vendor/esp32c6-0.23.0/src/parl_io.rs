#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    rx_cfg0: RX_CFG0,
    rx_cfg1: RX_CFG1,
    tx_cfg0: TX_CFG0,
    tx_cfg1: TX_CFG1,
    st: ST,
    int_ena: INT_ENA,
    int_raw: INT_RAW,
    int_st: INT_ST,
    int_clr: INT_CLR,
    _reserved9: [u8; 0xfc],
    clk: CLK,
    _reserved10: [u8; 0x02d8],
    version: VERSION,
}
impl RegisterBlock {
    #[doc = "0x00 - Parallel RX module configuration register0."]
    #[inline(always)]
    pub const fn rx_cfg0(&self) -> &RX_CFG0 {
        &self.rx_cfg0
    }
    #[doc = "0x04 - Parallel RX module configuration register1."]
    #[inline(always)]
    pub const fn rx_cfg1(&self) -> &RX_CFG1 {
        &self.rx_cfg1
    }
    #[doc = "0x08 - Parallel TX module configuration register0."]
    #[inline(always)]
    pub const fn tx_cfg0(&self) -> &TX_CFG0 {
        &self.tx_cfg0
    }
    #[doc = "0x0c - Parallel TX module configuration register1."]
    #[inline(always)]
    pub const fn tx_cfg1(&self) -> &TX_CFG1 {
        &self.tx_cfg1
    }
    #[doc = "0x10 - Parallel IO module status register0."]
    #[inline(always)]
    pub const fn st(&self) -> &ST {
        &self.st
    }
    #[doc = "0x14 - Parallel IO interrupt enable singal configuration register."]
    #[inline(always)]
    pub const fn int_ena(&self) -> &INT_ENA {
        &self.int_ena
    }
    #[doc = "0x18 - Parallel IO interrupt raw singal status register."]
    #[inline(always)]
    pub const fn int_raw(&self) -> &INT_RAW {
        &self.int_raw
    }
    #[doc = "0x1c - Parallel IO interrupt singal status register."]
    #[inline(always)]
    pub const fn int_st(&self) -> &INT_ST {
        &self.int_st
    }
    #[doc = "0x20 - Parallel IO interrupt clear singal configuration register."]
    #[inline(always)]
    pub const fn int_clr(&self) -> &INT_CLR {
        &self.int_clr
    }
    #[doc = "0x120 - Parallel IO clk configuration register"]
    #[inline(always)]
    pub const fn clk(&self) -> &CLK {
        &self.clk
    }
    #[doc = "0x3fc - Version register."]
    #[inline(always)]
    pub const fn version(&self) -> &VERSION {
        &self.version
    }
}
#[doc = "RX_CFG0 (rw) register accessor: Parallel RX module configuration register0.\n\nYou can [`read`](crate::Reg::read) this register and get [`rx_cfg0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rx_cfg0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rx_cfg0`] module"]
pub type RX_CFG0 = crate::Reg<rx_cfg0::RX_CFG0_SPEC>;
#[doc = "Parallel RX module configuration register0."]
pub mod rx_cfg0;
#[doc = "RX_CFG1 (rw) register accessor: Parallel RX module configuration register1.\n\nYou can [`read`](crate::Reg::read) this register and get [`rx_cfg1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rx_cfg1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rx_cfg1`] module"]
pub type RX_CFG1 = crate::Reg<rx_cfg1::RX_CFG1_SPEC>;
#[doc = "Parallel RX module configuration register1."]
pub mod rx_cfg1;
#[doc = "TX_CFG0 (rw) register accessor: Parallel TX module configuration register0.\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_cfg0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_cfg0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tx_cfg0`] module"]
pub type TX_CFG0 = crate::Reg<tx_cfg0::TX_CFG0_SPEC>;
#[doc = "Parallel TX module configuration register0."]
pub mod tx_cfg0;
#[doc = "TX_CFG1 (rw) register accessor: Parallel TX module configuration register1.\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_cfg1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_cfg1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tx_cfg1`] module"]
pub type TX_CFG1 = crate::Reg<tx_cfg1::TX_CFG1_SPEC>;
#[doc = "Parallel TX module configuration register1."]
pub mod tx_cfg1;
#[doc = "ST (r) register accessor: Parallel IO module status register0.\n\nYou can [`read`](crate::Reg::read) this register and get [`st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st`] module"]
pub type ST = crate::Reg<st::ST_SPEC>;
#[doc = "Parallel IO module status register0."]
pub mod st;
#[doc = "INT_ENA (rw) register accessor: Parallel IO interrupt enable singal configuration register.\n\nYou can [`read`](crate::Reg::read) this register and get [`int_ena::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_ena::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_ena`] module"]
pub type INT_ENA = crate::Reg<int_ena::INT_ENA_SPEC>;
#[doc = "Parallel IO interrupt enable singal configuration register."]
pub mod int_ena;
#[doc = "INT_RAW (rw) register accessor: Parallel IO interrupt raw singal status register.\n\nYou can [`read`](crate::Reg::read) this register and get [`int_raw::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_raw::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_raw`] module"]
pub type INT_RAW = crate::Reg<int_raw::INT_RAW_SPEC>;
#[doc = "Parallel IO interrupt raw singal status register."]
pub mod int_raw;
#[doc = "INT_ST (r) register accessor: Parallel IO interrupt singal status register.\n\nYou can [`read`](crate::Reg::read) this register and get [`int_st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_st`] module"]
pub type INT_ST = crate::Reg<int_st::INT_ST_SPEC>;
#[doc = "Parallel IO interrupt singal status register."]
pub mod int_st;
#[doc = "INT_CLR (w) register accessor: Parallel IO interrupt clear singal configuration register.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_clr::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_clr`] module"]
pub type INT_CLR = crate::Reg<int_clr::INT_CLR_SPEC>;
#[doc = "Parallel IO interrupt clear singal configuration register."]
pub mod int_clr;
#[doc = "CLK (rw) register accessor: Parallel IO clk configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`clk::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clk::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@clk`] module"]
pub type CLK = crate::Reg<clk::CLK_SPEC>;
#[doc = "Parallel IO clk configuration register"]
pub mod clk;
pub use crate::aes::{date as version, DATE as VERSION};
