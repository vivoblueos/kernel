#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    chdata: [CHDATA; 4],
    ch_tx_conf0: [CH_TX_CONF0; 2],
    ch_rx_conf0: (),
    _reserved3: [u8; 0x04],
    ch_rx_conf1: (),
    _reserved4: [u8; 0x0c],
    ch_tx_status: [CH_TX_STATUS; 2],
    ch_rx_status: [CH_RX_STATUS; 2],
    int_raw: INT_RAW,
    int_st: INT_ST,
    int_ena: INT_ENA,
    int_clr: INT_CLR,
    chcarrier_duty: [CHCARRIER_DUTY; 2],
    ch_rx_carrier_rm: [CH_RX_CARRIER_RM; 2],
    ch_tx_lim: [CH_TX_LIM; 2],
    ch_rx_lim: [CH_RX_LIM; 2],
    sys_conf: SYS_CONF,
    tx_sim: TX_SIM,
    ref_cnt_rst: REF_CNT_RST,
    _reserved17: [u8; 0x58],
    date: DATE,
}
impl RegisterBlock {
    #[doc = "0x00..0x10 - The read and write data register for CHANNEL%s by apb fifo access."]
    #[inline(always)]
    pub const fn chdata(&self, n: usize) -> &CHDATA {
        &self.chdata[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x00..0x10 - The read and write data register for CHANNEL%s by apb fifo access."]
    #[inline(always)]
    pub fn chdata_iter(&self) -> impl Iterator<Item = &CHDATA> {
        self.chdata.iter()
    }
    #[doc = "0x00 - The read and write data register for CHANNEL0 by apb fifo access."]
    #[inline(always)]
    pub const fn ch0data(&self) -> &CHDATA {
        self.chdata(0)
    }
    #[doc = "0x04 - The read and write data register for CHANNEL1 by apb fifo access."]
    #[inline(always)]
    pub const fn ch1data(&self) -> &CHDATA {
        self.chdata(1)
    }
    #[doc = "0x08 - The read and write data register for CHANNEL2 by apb fifo access."]
    #[inline(always)]
    pub const fn ch2data(&self) -> &CHDATA {
        self.chdata(2)
    }
    #[doc = "0x0c - The read and write data register for CHANNEL3 by apb fifo access."]
    #[inline(always)]
    pub const fn ch3data(&self) -> &CHDATA {
        self.chdata(3)
    }
    #[doc = "0x10..0x18 - Channel %s configure register 0"]
    #[inline(always)]
    pub const fn ch_tx_conf0(&self, n: usize) -> &CH_TX_CONF0 {
        &self.ch_tx_conf0[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x10..0x18 - Channel %s configure register 0"]
    #[inline(always)]
    pub fn ch_tx_conf0_iter(&self) -> impl Iterator<Item = &CH_TX_CONF0> {
        self.ch_tx_conf0.iter()
    }
    #[doc = "0x10 - Channel 0 configure register 0"]
    #[inline(always)]
    pub const fn ch0_tx_conf0(&self) -> &CH_TX_CONF0 {
        self.ch_tx_conf0(0)
    }
    #[doc = "0x14 - Channel 1 configure register 0"]
    #[inline(always)]
    pub const fn ch1_tx_conf0(&self) -> &CH_TX_CONF0 {
        self.ch_tx_conf0(1)
    }
    #[doc = "0x18..0x20 - Channel %s configure register 0"]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is the index of register in the array. `n == 0` corresponds to `CH2_RX_CONF0` register.</div>"]
    #[inline(always)]
    pub const fn ch_rx_conf0(&self, n: usize) -> &CH_RX_CONF0 {
        #[allow(clippy::no_effect)]
        [(); 2][n];
        unsafe {
            &*core::ptr::from_ref(self)
                .cast::<u8>()
                .add(24)
                .add(8 * n)
                .cast()
        }
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x18..0x20 - Channel %s configure register 0"]
    #[inline(always)]
    pub fn ch_rx_conf0_iter(&self) -> impl Iterator<Item = &CH_RX_CONF0> {
        (0..2).map(move |n| unsafe {
            &*core::ptr::from_ref(self)
                .cast::<u8>()
                .add(24)
                .add(8 * n)
                .cast()
        })
    }
    #[doc = "0x18 - Channel 2 configure register 0"]
    #[inline(always)]
    pub const fn ch2_rx_conf0(&self) -> &CH_RX_CONF0 {
        self.ch_rx_conf0(0)
    }
    #[doc = "0x20 - Channel 3 configure register 0"]
    #[inline(always)]
    pub const fn ch3_rx_conf0(&self) -> &CH_RX_CONF0 {
        self.ch_rx_conf0(1)
    }
    #[doc = "0x1c..0x24 - Channel %s configure register 1"]
    #[doc = ""]
    #[doc = "<div class=\"warning\">`n` is the index of register in the array. `n == 0` corresponds to `CH2_RX_CONF1` register.</div>"]
    #[inline(always)]
    pub const fn ch_rx_conf1(&self, n: usize) -> &CH_RX_CONF1 {
        #[allow(clippy::no_effect)]
        [(); 2][n];
        unsafe {
            &*core::ptr::from_ref(self)
                .cast::<u8>()
                .add(28)
                .add(8 * n)
                .cast()
        }
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x1c..0x24 - Channel %s configure register 1"]
    #[inline(always)]
    pub fn ch_rx_conf1_iter(&self) -> impl Iterator<Item = &CH_RX_CONF1> {
        (0..2).map(move |n| unsafe {
            &*core::ptr::from_ref(self)
                .cast::<u8>()
                .add(28)
                .add(8 * n)
                .cast()
        })
    }
    #[doc = "0x1c - Channel 2 configure register 1"]
    #[inline(always)]
    pub const fn ch2_rx_conf1(&self) -> &CH_RX_CONF1 {
        self.ch_rx_conf1(0)
    }
    #[doc = "0x24 - Channel 3 configure register 1"]
    #[inline(always)]
    pub const fn ch3_rx_conf1(&self) -> &CH_RX_CONF1 {
        self.ch_rx_conf1(1)
    }
    #[doc = "0x28..0x30 - Channel %s status register"]
    #[inline(always)]
    pub const fn ch_tx_status(&self, n: usize) -> &CH_TX_STATUS {
        &self.ch_tx_status[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x28..0x30 - Channel %s status register"]
    #[inline(always)]
    pub fn ch_tx_status_iter(&self) -> impl Iterator<Item = &CH_TX_STATUS> {
        self.ch_tx_status.iter()
    }
    #[doc = "0x28 - Channel 0 status register"]
    #[inline(always)]
    pub const fn ch0_tx_status(&self) -> &CH_TX_STATUS {
        self.ch_tx_status(0)
    }
    #[doc = "0x2c - Channel 1 status register"]
    #[inline(always)]
    pub const fn ch1_tx_status(&self) -> &CH_TX_STATUS {
        self.ch_tx_status(1)
    }
    #[doc = "0x30..0x38 - Channel %s status register"]
    #[inline(always)]
    pub const fn ch_rx_status(&self, n: usize) -> &CH_RX_STATUS {
        &self.ch_rx_status[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x30..0x38 - Channel %s status register"]
    #[inline(always)]
    pub fn ch_rx_status_iter(&self) -> impl Iterator<Item = &CH_RX_STATUS> {
        self.ch_rx_status.iter()
    }
    #[doc = "0x30 - Channel 0 status register"]
    #[inline(always)]
    pub const fn ch0_rx_status(&self) -> &CH_RX_STATUS {
        self.ch_rx_status(0)
    }
    #[doc = "0x34 - Channel 1 status register"]
    #[inline(always)]
    pub const fn ch1_rx_status(&self) -> &CH_RX_STATUS {
        self.ch_rx_status(1)
    }
    #[doc = "0x38 - Raw interrupt status"]
    #[inline(always)]
    pub const fn int_raw(&self) -> &INT_RAW {
        &self.int_raw
    }
    #[doc = "0x3c - Masked interrupt status"]
    #[inline(always)]
    pub const fn int_st(&self) -> &INT_ST {
        &self.int_st
    }
    #[doc = "0x40 - Interrupt enable bits"]
    #[inline(always)]
    pub const fn int_ena(&self) -> &INT_ENA {
        &self.int_ena
    }
    #[doc = "0x44 - Interrupt clear bits"]
    #[inline(always)]
    pub const fn int_clr(&self) -> &INT_CLR {
        &self.int_clr
    }
    #[doc = "0x48..0x50 - Channel %s duty cycle configuration register"]
    #[inline(always)]
    pub const fn chcarrier_duty(&self, n: usize) -> &CHCARRIER_DUTY {
        &self.chcarrier_duty[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x48..0x50 - Channel %s duty cycle configuration register"]
    #[inline(always)]
    pub fn chcarrier_duty_iter(&self) -> impl Iterator<Item = &CHCARRIER_DUTY> {
        self.chcarrier_duty.iter()
    }
    #[doc = "0x48 - Channel 0 duty cycle configuration register"]
    #[inline(always)]
    pub const fn ch0carrier_duty(&self) -> &CHCARRIER_DUTY {
        self.chcarrier_duty(0)
    }
    #[doc = "0x4c - Channel 1 duty cycle configuration register"]
    #[inline(always)]
    pub const fn ch1carrier_duty(&self) -> &CHCARRIER_DUTY {
        self.chcarrier_duty(1)
    }
    #[doc = "0x50..0x58 - Channel %s carrier remove register"]
    #[inline(always)]
    pub const fn ch_rx_carrier_rm(&self, n: usize) -> &CH_RX_CARRIER_RM {
        &self.ch_rx_carrier_rm[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x50..0x58 - Channel %s carrier remove register"]
    #[inline(always)]
    pub fn ch_rx_carrier_rm_iter(&self) -> impl Iterator<Item = &CH_RX_CARRIER_RM> {
        self.ch_rx_carrier_rm.iter()
    }
    #[doc = "0x50 - Channel 0 carrier remove register"]
    #[inline(always)]
    pub const fn ch0_rx_carrier_rm(&self) -> &CH_RX_CARRIER_RM {
        self.ch_rx_carrier_rm(0)
    }
    #[doc = "0x54 - Channel 1 carrier remove register"]
    #[inline(always)]
    pub const fn ch1_rx_carrier_rm(&self) -> &CH_RX_CARRIER_RM {
        self.ch_rx_carrier_rm(1)
    }
    #[doc = "0x58..0x60 - Channel %s Tx event configuration register"]
    #[inline(always)]
    pub const fn ch_tx_lim(&self, n: usize) -> &CH_TX_LIM {
        &self.ch_tx_lim[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x58..0x60 - Channel %s Tx event configuration register"]
    #[inline(always)]
    pub fn ch_tx_lim_iter(&self) -> impl Iterator<Item = &CH_TX_LIM> {
        self.ch_tx_lim.iter()
    }
    #[doc = "0x58 - Channel 0 Tx event configuration register"]
    #[inline(always)]
    pub const fn ch0_tx_lim(&self) -> &CH_TX_LIM {
        self.ch_tx_lim(0)
    }
    #[doc = "0x5c - Channel 1 Tx event configuration register"]
    #[inline(always)]
    pub const fn ch1_tx_lim(&self) -> &CH_TX_LIM {
        self.ch_tx_lim(1)
    }
    #[doc = "0x60..0x68 - Channel %s Rx event configuration register"]
    #[inline(always)]
    pub const fn ch_rx_lim(&self, n: usize) -> &CH_RX_LIM {
        &self.ch_rx_lim[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x60..0x68 - Channel %s Rx event configuration register"]
    #[inline(always)]
    pub fn ch_rx_lim_iter(&self) -> impl Iterator<Item = &CH_RX_LIM> {
        self.ch_rx_lim.iter()
    }
    #[doc = "0x60 - Channel 0 Rx event configuration register"]
    #[inline(always)]
    pub const fn ch0_rx_lim(&self) -> &CH_RX_LIM {
        self.ch_rx_lim(0)
    }
    #[doc = "0x64 - Channel 1 Rx event configuration register"]
    #[inline(always)]
    pub const fn ch1_rx_lim(&self) -> &CH_RX_LIM {
        self.ch_rx_lim(1)
    }
    #[doc = "0x68 - RMT apb configuration register"]
    #[inline(always)]
    pub const fn sys_conf(&self) -> &SYS_CONF {
        &self.sys_conf
    }
    #[doc = "0x6c - RMT TX synchronous register"]
    #[inline(always)]
    pub const fn tx_sim(&self) -> &TX_SIM {
        &self.tx_sim
    }
    #[doc = "0x70 - RMT clock divider reset register"]
    #[inline(always)]
    pub const fn ref_cnt_rst(&self) -> &REF_CNT_RST {
        &self.ref_cnt_rst
    }
    #[doc = "0xcc - RMT version register"]
    #[inline(always)]
    pub const fn date(&self) -> &DATE {
        &self.date
    }
}
#[doc = "CHDATA (rw) register accessor: The read and write data register for CHANNEL%s by apb fifo access.\n\nYou can [`read`](crate::Reg::read) this register and get [`chdata::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`chdata::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@chdata`] module"]
pub type CHDATA = crate::Reg<chdata::CHDATA_SPEC>;
#[doc = "The read and write data register for CHANNEL%s by apb fifo access."]
pub mod chdata;
#[doc = "CH_TX_CONF0 (rw) register accessor: Channel %s configure register 0\n\nYou can [`read`](crate::Reg::read) this register and get [`ch_tx_conf0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ch_tx_conf0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch_tx_conf0`] module"]
pub type CH_TX_CONF0 = crate::Reg<ch_tx_conf0::CH_TX_CONF0_SPEC>;
#[doc = "Channel %s configure register 0"]
pub mod ch_tx_conf0;
#[doc = "CH_RX_CONF0 (rw) register accessor: Channel %s configure register 0\n\nYou can [`read`](crate::Reg::read) this register and get [`ch_rx_conf0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ch_rx_conf0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch_rx_conf0`] module"]
pub type CH_RX_CONF0 = crate::Reg<ch_rx_conf0::CH_RX_CONF0_SPEC>;
#[doc = "Channel %s configure register 0"]
pub mod ch_rx_conf0;
#[doc = "CH_RX_CONF1 (rw) register accessor: Channel %s configure register 1\n\nYou can [`read`](crate::Reg::read) this register and get [`ch_rx_conf1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ch_rx_conf1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch_rx_conf1`] module"]
pub type CH_RX_CONF1 = crate::Reg<ch_rx_conf1::CH_RX_CONF1_SPEC>;
#[doc = "Channel %s configure register 1"]
pub mod ch_rx_conf1;
#[doc = "CH_TX_STATUS (r) register accessor: Channel %s status register\n\nYou can [`read`](crate::Reg::read) this register and get [`ch_tx_status::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch_tx_status`] module"]
pub type CH_TX_STATUS = crate::Reg<ch_tx_status::CH_TX_STATUS_SPEC>;
#[doc = "Channel %s status register"]
pub mod ch_tx_status;
#[doc = "CH_RX_STATUS (r) register accessor: Channel %s status register\n\nYou can [`read`](crate::Reg::read) this register and get [`ch_rx_status::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch_rx_status`] module"]
pub type CH_RX_STATUS = crate::Reg<ch_rx_status::CH_RX_STATUS_SPEC>;
#[doc = "Channel %s status register"]
pub mod ch_rx_status;
#[doc = "INT_RAW (rw) register accessor: Raw interrupt status\n\nYou can [`read`](crate::Reg::read) this register and get [`int_raw::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_raw::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_raw`] module"]
pub type INT_RAW = crate::Reg<int_raw::INT_RAW_SPEC>;
#[doc = "Raw interrupt status"]
pub mod int_raw;
#[doc = "INT_ST (r) register accessor: Masked interrupt status\n\nYou can [`read`](crate::Reg::read) this register and get [`int_st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_st`] module"]
pub type INT_ST = crate::Reg<int_st::INT_ST_SPEC>;
#[doc = "Masked interrupt status"]
pub mod int_st;
#[doc = "INT_ENA (rw) register accessor: Interrupt enable bits\n\nYou can [`read`](crate::Reg::read) this register and get [`int_ena::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_ena::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_ena`] module"]
pub type INT_ENA = crate::Reg<int_ena::INT_ENA_SPEC>;
#[doc = "Interrupt enable bits"]
pub mod int_ena;
#[doc = "INT_CLR (w) register accessor: Interrupt clear bits\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_clr::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_clr`] module"]
pub type INT_CLR = crate::Reg<int_clr::INT_CLR_SPEC>;
#[doc = "Interrupt clear bits"]
pub mod int_clr;
#[doc = "CHCARRIER_DUTY (rw) register accessor: Channel %s duty cycle configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`chcarrier_duty::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`chcarrier_duty::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@chcarrier_duty`] module"]
pub type CHCARRIER_DUTY = crate::Reg<chcarrier_duty::CHCARRIER_DUTY_SPEC>;
#[doc = "Channel %s duty cycle configuration register"]
pub mod chcarrier_duty;
#[doc = "CH_RX_CARRIER_RM (rw) register accessor: Channel %s carrier remove register\n\nYou can [`read`](crate::Reg::read) this register and get [`ch_rx_carrier_rm::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ch_rx_carrier_rm::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch_rx_carrier_rm`] module"]
pub type CH_RX_CARRIER_RM = crate::Reg<ch_rx_carrier_rm::CH_RX_CARRIER_RM_SPEC>;
#[doc = "Channel %s carrier remove register"]
pub mod ch_rx_carrier_rm;
#[doc = "CH_TX_LIM (rw) register accessor: Channel %s Tx event configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`ch_tx_lim::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ch_tx_lim::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch_tx_lim`] module"]
pub type CH_TX_LIM = crate::Reg<ch_tx_lim::CH_TX_LIM_SPEC>;
#[doc = "Channel %s Tx event configuration register"]
pub mod ch_tx_lim;
#[doc = "CH_RX_LIM (rw) register accessor: Channel %s Rx event configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`ch_rx_lim::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ch_rx_lim::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ch_rx_lim`] module"]
pub type CH_RX_LIM = crate::Reg<ch_rx_lim::CH_RX_LIM_SPEC>;
#[doc = "Channel %s Rx event configuration register"]
pub mod ch_rx_lim;
#[doc = "SYS_CONF (rw) register accessor: RMT apb configuration register\n\nYou can [`read`](crate::Reg::read) this register and get [`sys_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sys_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sys_conf`] module"]
pub type SYS_CONF = crate::Reg<sys_conf::SYS_CONF_SPEC>;
#[doc = "RMT apb configuration register"]
pub mod sys_conf;
#[doc = "TX_SIM (rw) register accessor: RMT TX synchronous register\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_sim::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_sim::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tx_sim`] module"]
pub type TX_SIM = crate::Reg<tx_sim::TX_SIM_SPEC>;
#[doc = "RMT TX synchronous register"]
pub mod tx_sim;
#[doc = "REF_CNT_RST (w) register accessor: RMT clock divider reset register\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ref_cnt_rst::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ref_cnt_rst`] module"]
pub type REF_CNT_RST = crate::Reg<ref_cnt_rst::REF_CNT_RST_SPEC>;
#[doc = "RMT clock divider reset register"]
pub mod ref_cnt_rst;
pub use crate::aes::{date, DATE};
