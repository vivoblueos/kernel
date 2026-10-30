#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    test_conf: TEST_CONF,
    lp_timer_conf: LP_TIMER_CONF,
    coex_lp_clk_conf: COEX_LP_CLK_CONF,
    wifi_lp_clk_conf: WIFI_LP_CLK_CONF,
    i2c_mst_clk_conf: I2C_MST_CLK_CONF,
    modem_32k_clk_conf: MODEM_32K_CLK_CONF,
    clk_conf: CLK_CONF,
    clk_conf_force_on: CLK_CONF_FORCE_ON,
    clk_conf_power_st: CLK_CONF_POWER_ST,
    rst_conf: RST_CONF,
    mem_conf: MEM_CONF,
    date: DATE,
}
impl RegisterBlock {
    #[doc = "0x00 - "]
    #[inline(always)]
    pub const fn test_conf(&self) -> &TEST_CONF {
        &self.test_conf
    }
    #[doc = "0x04 - "]
    #[inline(always)]
    pub const fn lp_timer_conf(&self) -> &LP_TIMER_CONF {
        &self.lp_timer_conf
    }
    #[doc = "0x08 - "]
    #[inline(always)]
    pub const fn coex_lp_clk_conf(&self) -> &COEX_LP_CLK_CONF {
        &self.coex_lp_clk_conf
    }
    #[doc = "0x0c - "]
    #[inline(always)]
    pub const fn wifi_lp_clk_conf(&self) -> &WIFI_LP_CLK_CONF {
        &self.wifi_lp_clk_conf
    }
    #[doc = "0x10 - "]
    #[inline(always)]
    pub const fn i2c_mst_clk_conf(&self) -> &I2C_MST_CLK_CONF {
        &self.i2c_mst_clk_conf
    }
    #[doc = "0x14 - "]
    #[inline(always)]
    pub const fn modem_32k_clk_conf(&self) -> &MODEM_32K_CLK_CONF {
        &self.modem_32k_clk_conf
    }
    #[doc = "0x18 - "]
    #[inline(always)]
    pub const fn clk_conf(&self) -> &CLK_CONF {
        &self.clk_conf
    }
    #[doc = "0x1c - "]
    #[inline(always)]
    pub const fn clk_conf_force_on(&self) -> &CLK_CONF_FORCE_ON {
        &self.clk_conf_force_on
    }
    #[doc = "0x20 - "]
    #[inline(always)]
    pub const fn clk_conf_power_st(&self) -> &CLK_CONF_POWER_ST {
        &self.clk_conf_power_st
    }
    #[doc = "0x24 - "]
    #[inline(always)]
    pub const fn rst_conf(&self) -> &RST_CONF {
        &self.rst_conf
    }
    #[doc = "0x28 - "]
    #[inline(always)]
    pub const fn mem_conf(&self) -> &MEM_CONF {
        &self.mem_conf
    }
    #[doc = "0x2c - AES version control register"]
    #[inline(always)]
    pub const fn date(&self) -> &DATE {
        &self.date
    }
}
#[doc = "TEST_CONF (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`test_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`test_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@test_conf`] module"]
pub type TEST_CONF = crate::Reg<test_conf::TEST_CONF_SPEC>;
#[doc = ""]
pub mod test_conf;
#[doc = "LP_TIMER_CONF (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`lp_timer_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`lp_timer_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@lp_timer_conf`] module"]
pub type LP_TIMER_CONF = crate::Reg<lp_timer_conf::LP_TIMER_CONF_SPEC>;
#[doc = ""]
pub mod lp_timer_conf;
#[doc = "COEX_LP_CLK_CONF (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`coex_lp_clk_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`coex_lp_clk_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@coex_lp_clk_conf`] module"]
pub type COEX_LP_CLK_CONF = crate::Reg<coex_lp_clk_conf::COEX_LP_CLK_CONF_SPEC>;
#[doc = ""]
pub mod coex_lp_clk_conf;
#[doc = "WIFI_LP_CLK_CONF (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`wifi_lp_clk_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`wifi_lp_clk_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@wifi_lp_clk_conf`] module"]
pub type WIFI_LP_CLK_CONF = crate::Reg<wifi_lp_clk_conf::WIFI_LP_CLK_CONF_SPEC>;
#[doc = ""]
pub mod wifi_lp_clk_conf;
#[doc = "I2C_MST_CLK_CONF (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`i2c_mst_clk_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`i2c_mst_clk_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@i2c_mst_clk_conf`] module"]
pub type I2C_MST_CLK_CONF = crate::Reg<i2c_mst_clk_conf::I2C_MST_CLK_CONF_SPEC>;
#[doc = ""]
pub mod i2c_mst_clk_conf;
#[doc = "MODEM_32K_CLK_CONF (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`modem_32k_clk_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`modem_32k_clk_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@modem_32k_clk_conf`] module"]
pub type MODEM_32K_CLK_CONF = crate::Reg<modem_32k_clk_conf::MODEM_32K_CLK_CONF_SPEC>;
#[doc = ""]
pub mod modem_32k_clk_conf;
#[doc = "CLK_CONF (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`clk_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clk_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@clk_conf`] module"]
pub type CLK_CONF = crate::Reg<clk_conf::CLK_CONF_SPEC>;
#[doc = ""]
pub mod clk_conf;
#[doc = "CLK_CONF_FORCE_ON (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`clk_conf_force_on::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clk_conf_force_on::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@clk_conf_force_on`] module"]
pub type CLK_CONF_FORCE_ON = crate::Reg<clk_conf_force_on::CLK_CONF_FORCE_ON_SPEC>;
#[doc = ""]
pub mod clk_conf_force_on;
#[doc = "CLK_CONF_POWER_ST (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`clk_conf_power_st::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clk_conf_power_st::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@clk_conf_power_st`] module"]
pub type CLK_CONF_POWER_ST = crate::Reg<clk_conf_power_st::CLK_CONF_POWER_ST_SPEC>;
#[doc = ""]
pub mod clk_conf_power_st;
#[doc = "RST_CONF (w) register accessor: \n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rst_conf::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rst_conf`] module"]
pub type RST_CONF = crate::Reg<rst_conf::RST_CONF_SPEC>;
#[doc = ""]
pub mod rst_conf;
#[doc = "MEM_CONF (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`mem_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mem_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mem_conf`] module"]
pub type MEM_CONF = crate::Reg<mem_conf::MEM_CONF_SPEC>;
#[doc = ""]
pub mod mem_conf;
pub use crate::aes::{date, DATE};
