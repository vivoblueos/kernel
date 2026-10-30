#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    scl_low_period: SCL_LOW_PERIOD,
    ctr: CTR,
    sr: SR,
    to: TO,
    slave_addr: SLAVE_ADDR,
    fifo_st: FIFO_ST,
    fifo_conf: FIFO_CONF,
    data: DATA,
    int_raw: INT_RAW,
    int_clr: INT_CLR,
    int_ena: INT_ENA,
    int_st: INT_ST,
    sda_hold: SDA_HOLD,
    sda_sample: SDA_SAMPLE,
    scl_high_period: SCL_HIGH_PERIOD,
    _reserved15: [u8; 0x04],
    scl_start_hold: SCL_START_HOLD,
    scl_rstart_setup: SCL_RSTART_SETUP,
    scl_stop_hold: SCL_STOP_HOLD,
    scl_stop_setup: SCL_STOP_SETUP,
    filter_cfg: FILTER_CFG,
    clk_conf: CLK_CONF,
    comd: [COMD; 8],
    scl_st_time_out: SCL_ST_TIME_OUT,
    scl_main_st_time_out: SCL_MAIN_ST_TIME_OUT,
    scl_sp_conf: SCL_SP_CONF,
    scl_stretch_conf: SCL_STRETCH_CONF,
    _reserved26: [u8; 0x70],
    date: DATE,
    _reserved27: [u8; 0x04],
    txfifo_start_addr: TXFIFO_START_ADDR,
    _reserved28: [u8; 0x7c],
    rxfifo_start_addr: RXFIFO_START_ADDR,
}
impl RegisterBlock {
    #[doc = "0x00 - I2C_SCL_LOW_PERIOD_REG"]
    #[inline(always)]
    pub const fn scl_low_period(&self) -> &SCL_LOW_PERIOD {
        &self.scl_low_period
    }
    #[doc = "0x04 - I2C_CTR_REG"]
    #[inline(always)]
    pub const fn ctr(&self) -> &CTR {
        &self.ctr
    }
    #[doc = "0x08 - I2C_SR_REG"]
    #[inline(always)]
    pub const fn sr(&self) -> &SR {
        &self.sr
    }
    #[doc = "0x0c - I2C_TO_REG"]
    #[inline(always)]
    pub const fn to(&self) -> &TO {
        &self.to
    }
    #[doc = "0x10 - I2C_SLAVE_ADDR_REG"]
    #[inline(always)]
    pub const fn slave_addr(&self) -> &SLAVE_ADDR {
        &self.slave_addr
    }
    #[doc = "0x14 - I2C_FIFO_ST_REG"]
    #[inline(always)]
    pub const fn fifo_st(&self) -> &FIFO_ST {
        &self.fifo_st
    }
    #[doc = "0x18 - I2C_FIFO_CONF_REG"]
    #[inline(always)]
    pub const fn fifo_conf(&self) -> &FIFO_CONF {
        &self.fifo_conf
    }
    #[doc = "0x1c - I2C_FIFO_DATA_REG"]
    #[inline(always)]
    pub const fn data(&self) -> &DATA {
        &self.data
    }
    #[doc = "0x20 - I2C_INT_RAW_REG"]
    #[inline(always)]
    pub const fn int_raw(&self) -> &INT_RAW {
        &self.int_raw
    }
    #[doc = "0x24 - I2C_INT_CLR_REG"]
    #[inline(always)]
    pub const fn int_clr(&self) -> &INT_CLR {
        &self.int_clr
    }
    #[doc = "0x28 - I2C_INT_ENA_REG"]
    #[inline(always)]
    pub const fn int_ena(&self) -> &INT_ENA {
        &self.int_ena
    }
    #[doc = "0x2c - I2C_INT_STATUS_REG"]
    #[inline(always)]
    pub const fn int_st(&self) -> &INT_ST {
        &self.int_st
    }
    #[doc = "0x30 - I2C_SDA_HOLD_REG"]
    #[inline(always)]
    pub const fn sda_hold(&self) -> &SDA_HOLD {
        &self.sda_hold
    }
    #[doc = "0x34 - I2C_SDA_SAMPLE_REG"]
    #[inline(always)]
    pub const fn sda_sample(&self) -> &SDA_SAMPLE {
        &self.sda_sample
    }
    #[doc = "0x38 - I2C_SCL_HIGH_PERIOD_REG"]
    #[inline(always)]
    pub const fn scl_high_period(&self) -> &SCL_HIGH_PERIOD {
        &self.scl_high_period
    }
    #[doc = "0x40 - I2C_SCL_START_HOLD_REG"]
    #[inline(always)]
    pub const fn scl_start_hold(&self) -> &SCL_START_HOLD {
        &self.scl_start_hold
    }
    #[doc = "0x44 - I2C_SCL_RSTART_SETUP_REG"]
    #[inline(always)]
    pub const fn scl_rstart_setup(&self) -> &SCL_RSTART_SETUP {
        &self.scl_rstart_setup
    }
    #[doc = "0x48 - I2C_SCL_STOP_HOLD_REG"]
    #[inline(always)]
    pub const fn scl_stop_hold(&self) -> &SCL_STOP_HOLD {
        &self.scl_stop_hold
    }
    #[doc = "0x4c - I2C_SCL_STOP_SETUP_REG"]
    #[inline(always)]
    pub const fn scl_stop_setup(&self) -> &SCL_STOP_SETUP {
        &self.scl_stop_setup
    }
    #[doc = "0x50 - I2C_FILTER_CFG_REG"]
    #[inline(always)]
    pub const fn filter_cfg(&self) -> &FILTER_CFG {
        &self.filter_cfg
    }
    #[doc = "0x54 - I2C_CLK_CONF_REG"]
    #[inline(always)]
    pub const fn clk_conf(&self) -> &CLK_CONF {
        &self.clk_conf
    }
    #[doc = "0x58..0x78 - I2C_COMD%s_REG"]
    #[inline(always)]
    pub const fn comd(&self, n: usize) -> &COMD {
        &self.comd[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x58..0x78 - I2C_COMD%s_REG"]
    #[inline(always)]
    pub fn comd_iter(&self) -> impl Iterator<Item = &COMD> {
        self.comd.iter()
    }
    #[doc = "0x78 - I2C_SCL_ST_TIME_OUT_REG"]
    #[inline(always)]
    pub const fn scl_st_time_out(&self) -> &SCL_ST_TIME_OUT {
        &self.scl_st_time_out
    }
    #[doc = "0x7c - I2C_SCL_MAIN_ST_TIME_OUT_REG"]
    #[inline(always)]
    pub const fn scl_main_st_time_out(&self) -> &SCL_MAIN_ST_TIME_OUT {
        &self.scl_main_st_time_out
    }
    #[doc = "0x80 - I2C_SCL_SP_CONF_REG"]
    #[inline(always)]
    pub const fn scl_sp_conf(&self) -> &SCL_SP_CONF {
        &self.scl_sp_conf
    }
    #[doc = "0x84 - I2C_SCL_STRETCH_CONF_REG"]
    #[inline(always)]
    pub const fn scl_stretch_conf(&self) -> &SCL_STRETCH_CONF {
        &self.scl_stretch_conf
    }
    #[doc = "0xf8 - I2C_DATE_REG"]
    #[inline(always)]
    pub const fn date(&self) -> &DATE {
        &self.date
    }
    #[doc = "0x100 - I2C_TXFIFO_START_ADDR_REG"]
    #[inline(always)]
    pub const fn txfifo_start_addr(&self) -> &TXFIFO_START_ADDR {
        &self.txfifo_start_addr
    }
    #[doc = "0x180 - I2C_RXFIFO_START_ADDR_REG"]
    #[inline(always)]
    pub const fn rxfifo_start_addr(&self) -> &RXFIFO_START_ADDR {
        &self.rxfifo_start_addr
    }
}
#[doc = "SCL_LOW_PERIOD (rw) register accessor: I2C_SCL_LOW_PERIOD_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`scl_low_period::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`scl_low_period::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@scl_low_period`] module"]
pub type SCL_LOW_PERIOD = crate::Reg<scl_low_period::SCL_LOW_PERIOD_SPEC>;
#[doc = "I2C_SCL_LOW_PERIOD_REG"]
pub mod scl_low_period;
#[doc = "CTR (rw) register accessor: I2C_CTR_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`ctr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ctr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ctr`] module"]
pub type CTR = crate::Reg<ctr::CTR_SPEC>;
#[doc = "I2C_CTR_REG"]
pub mod ctr;
#[doc = "SR (r) register accessor: I2C_SR_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`sr::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sr`] module"]
pub type SR = crate::Reg<sr::SR_SPEC>;
#[doc = "I2C_SR_REG"]
pub mod sr;
#[doc = "TO (rw) register accessor: I2C_TO_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`to::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`to::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@to`] module"]
pub type TO = crate::Reg<to::TO_SPEC>;
#[doc = "I2C_TO_REG"]
pub mod to;
#[doc = "SLAVE_ADDR (rw) register accessor: I2C_SLAVE_ADDR_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`slave_addr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slave_addr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slave_addr`] module"]
pub type SLAVE_ADDR = crate::Reg<slave_addr::SLAVE_ADDR_SPEC>;
#[doc = "I2C_SLAVE_ADDR_REG"]
pub mod slave_addr;
#[doc = "FIFO_ST (r) register accessor: I2C_FIFO_ST_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`fifo_st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@fifo_st`] module"]
pub type FIFO_ST = crate::Reg<fifo_st::FIFO_ST_SPEC>;
#[doc = "I2C_FIFO_ST_REG"]
pub mod fifo_st;
#[doc = "FIFO_CONF (rw) register accessor: I2C_FIFO_CONF_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`fifo_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`fifo_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@fifo_conf`] module"]
pub type FIFO_CONF = crate::Reg<fifo_conf::FIFO_CONF_SPEC>;
#[doc = "I2C_FIFO_CONF_REG"]
pub mod fifo_conf;
#[doc = "DATA (rw) register accessor: I2C_FIFO_DATA_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`data::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`data::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data`] module"]
pub type DATA = crate::Reg<data::DATA_SPEC>;
#[doc = "I2C_FIFO_DATA_REG"]
pub mod data;
#[doc = "INT_RAW (r) register accessor: I2C_INT_RAW_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`int_raw::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_raw`] module"]
pub type INT_RAW = crate::Reg<int_raw::INT_RAW_SPEC>;
#[doc = "I2C_INT_RAW_REG"]
pub mod int_raw;
#[doc = "INT_CLR (w) register accessor: I2C_INT_CLR_REG\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_clr::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_clr`] module"]
pub type INT_CLR = crate::Reg<int_clr::INT_CLR_SPEC>;
#[doc = "I2C_INT_CLR_REG"]
pub mod int_clr;
#[doc = "INT_ENA (rw) register accessor: I2C_INT_ENA_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`int_ena::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_ena::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_ena`] module"]
pub type INT_ENA = crate::Reg<int_ena::INT_ENA_SPEC>;
#[doc = "I2C_INT_ENA_REG"]
pub mod int_ena;
#[doc = "INT_ST (r) register accessor: I2C_INT_STATUS_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`int_st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_st`] module"]
pub type INT_ST = crate::Reg<int_st::INT_ST_SPEC>;
#[doc = "I2C_INT_STATUS_REG"]
pub mod int_st;
#[doc = "SDA_HOLD (rw) register accessor: I2C_SDA_HOLD_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`sda_hold::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sda_hold::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sda_hold`] module"]
pub type SDA_HOLD = crate::Reg<sda_hold::SDA_HOLD_SPEC>;
#[doc = "I2C_SDA_HOLD_REG"]
pub mod sda_hold;
#[doc = "SDA_SAMPLE (rw) register accessor: I2C_SDA_SAMPLE_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`sda_sample::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sda_sample::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sda_sample`] module"]
pub type SDA_SAMPLE = crate::Reg<sda_sample::SDA_SAMPLE_SPEC>;
#[doc = "I2C_SDA_SAMPLE_REG"]
pub mod sda_sample;
#[doc = "SCL_HIGH_PERIOD (rw) register accessor: I2C_SCL_HIGH_PERIOD_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`scl_high_period::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`scl_high_period::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@scl_high_period`] module"]
pub type SCL_HIGH_PERIOD = crate::Reg<scl_high_period::SCL_HIGH_PERIOD_SPEC>;
#[doc = "I2C_SCL_HIGH_PERIOD_REG"]
pub mod scl_high_period;
#[doc = "SCL_START_HOLD (rw) register accessor: I2C_SCL_START_HOLD_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`scl_start_hold::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`scl_start_hold::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@scl_start_hold`] module"]
pub type SCL_START_HOLD = crate::Reg<scl_start_hold::SCL_START_HOLD_SPEC>;
#[doc = "I2C_SCL_START_HOLD_REG"]
pub mod scl_start_hold;
#[doc = "SCL_RSTART_SETUP (rw) register accessor: I2C_SCL_RSTART_SETUP_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`scl_rstart_setup::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`scl_rstart_setup::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@scl_rstart_setup`] module"]
pub type SCL_RSTART_SETUP = crate::Reg<scl_rstart_setup::SCL_RSTART_SETUP_SPEC>;
#[doc = "I2C_SCL_RSTART_SETUP_REG"]
pub mod scl_rstart_setup;
#[doc = "SCL_STOP_HOLD (rw) register accessor: I2C_SCL_STOP_HOLD_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`scl_stop_hold::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`scl_stop_hold::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@scl_stop_hold`] module"]
pub type SCL_STOP_HOLD = crate::Reg<scl_stop_hold::SCL_STOP_HOLD_SPEC>;
#[doc = "I2C_SCL_STOP_HOLD_REG"]
pub mod scl_stop_hold;
#[doc = "SCL_STOP_SETUP (rw) register accessor: I2C_SCL_STOP_SETUP_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`scl_stop_setup::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`scl_stop_setup::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@scl_stop_setup`] module"]
pub type SCL_STOP_SETUP = crate::Reg<scl_stop_setup::SCL_STOP_SETUP_SPEC>;
#[doc = "I2C_SCL_STOP_SETUP_REG"]
pub mod scl_stop_setup;
#[doc = "FILTER_CFG (rw) register accessor: I2C_FILTER_CFG_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`filter_cfg::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`filter_cfg::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@filter_cfg`] module"]
pub type FILTER_CFG = crate::Reg<filter_cfg::FILTER_CFG_SPEC>;
#[doc = "I2C_FILTER_CFG_REG"]
pub mod filter_cfg;
#[doc = "CLK_CONF (rw) register accessor: I2C_CLK_CONF_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`clk_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clk_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@clk_conf`] module"]
pub type CLK_CONF = crate::Reg<clk_conf::CLK_CONF_SPEC>;
#[doc = "I2C_CLK_CONF_REG"]
pub mod clk_conf;
#[doc = "COMD (rw) register accessor: I2C_COMD%s_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`comd::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`comd::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@comd`] module"]
pub type COMD = crate::Reg<comd::COMD_SPEC>;
#[doc = "I2C_COMD%s_REG"]
pub mod comd;
#[doc = "SCL_ST_TIME_OUT (rw) register accessor: I2C_SCL_ST_TIME_OUT_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`scl_st_time_out::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`scl_st_time_out::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@scl_st_time_out`] module"]
pub type SCL_ST_TIME_OUT = crate::Reg<scl_st_time_out::SCL_ST_TIME_OUT_SPEC>;
#[doc = "I2C_SCL_ST_TIME_OUT_REG"]
pub mod scl_st_time_out;
#[doc = "SCL_MAIN_ST_TIME_OUT (rw) register accessor: I2C_SCL_MAIN_ST_TIME_OUT_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`scl_main_st_time_out::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`scl_main_st_time_out::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@scl_main_st_time_out`] module"]
pub type SCL_MAIN_ST_TIME_OUT = crate::Reg<scl_main_st_time_out::SCL_MAIN_ST_TIME_OUT_SPEC>;
#[doc = "I2C_SCL_MAIN_ST_TIME_OUT_REG"]
pub mod scl_main_st_time_out;
#[doc = "SCL_SP_CONF (rw) register accessor: I2C_SCL_SP_CONF_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`scl_sp_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`scl_sp_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@scl_sp_conf`] module"]
pub type SCL_SP_CONF = crate::Reg<scl_sp_conf::SCL_SP_CONF_SPEC>;
#[doc = "I2C_SCL_SP_CONF_REG"]
pub mod scl_sp_conf;
#[doc = "SCL_STRETCH_CONF (rw) register accessor: I2C_SCL_STRETCH_CONF_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`scl_stretch_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`scl_stretch_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@scl_stretch_conf`] module"]
pub type SCL_STRETCH_CONF = crate::Reg<scl_stretch_conf::SCL_STRETCH_CONF_SPEC>;
#[doc = "I2C_SCL_STRETCH_CONF_REG"]
pub mod scl_stretch_conf;
pub use crate::aes::{date, DATE};
#[doc = "TXFIFO_START_ADDR (r) register accessor: I2C_TXFIFO_START_ADDR_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`txfifo_start_addr::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@txfifo_start_addr`] module"]
pub type TXFIFO_START_ADDR = crate::Reg<txfifo_start_addr::TXFIFO_START_ADDR_SPEC>;
#[doc = "I2C_TXFIFO_START_ADDR_REG"]
pub mod txfifo_start_addr;
#[doc = "RXFIFO_START_ADDR (r) register accessor: I2C_RXFIFO_START_ADDR_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`rxfifo_start_addr::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rxfifo_start_addr`] module"]
pub type RXFIFO_START_ADDR = crate::Reg<rxfifo_start_addr::RXFIFO_START_ADDR_SPEC>;
#[doc = "I2C_RXFIFO_START_ADDR_REG"]
pub mod rxfifo_start_addr;
