#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    mode: MODE,
    cmd: CMD,
    status: STATUS,
    int_raw: INT_RAW,
    int_ena: INT_ENA,
    _reserved5: [u8; 0x04],
    bus_timing_0: BUS_TIMING_0,
    bus_timing_1: BUS_TIMING_1,
    _reserved7: [u8; 0x0c],
    arb_lost_cap: ARB_LOST_CAP,
    err_code_cap: ERR_CODE_CAP,
    err_warning_limit: ERR_WARNING_LIMIT,
    rx_err_cnt: RX_ERR_CNT,
    tx_err_cnt: TX_ERR_CNT,
    data: [DATA; 13],
    rx_message_cnt: RX_MESSAGE_CNT,
    _reserved14: [u8; 0x04],
    clock_divider: CLOCK_DIVIDER,
    sw_standby_cfg: SW_STANDBY_CFG,
    hw_cfg: HW_CFG,
    hw_standby_cnt: HW_STANDBY_CNT,
    idle_intr_cnt: IDLE_INTR_CNT,
    eco_cfg: ECO_CFG,
}
impl RegisterBlock {
    #[doc = "0x00 - TWAI mode register."]
    #[inline(always)]
    pub const fn mode(&self) -> &MODE {
        &self.mode
    }
    #[doc = "0x04 - TWAI command register."]
    #[inline(always)]
    pub const fn cmd(&self) -> &CMD {
        &self.cmd
    }
    #[doc = "0x08 - TWAI status register."]
    #[inline(always)]
    pub const fn status(&self) -> &STATUS {
        &self.status
    }
    #[doc = "0x0c - Interrupt signals' register."]
    #[inline(always)]
    pub const fn int_raw(&self) -> &INT_RAW {
        &self.int_raw
    }
    #[doc = "0x10 - Interrupt enable register."]
    #[inline(always)]
    pub const fn int_ena(&self) -> &INT_ENA {
        &self.int_ena
    }
    #[doc = "0x18 - Bit timing configuration register 0."]
    #[inline(always)]
    pub const fn bus_timing_0(&self) -> &BUS_TIMING_0 {
        &self.bus_timing_0
    }
    #[doc = "0x1c - Bit timing configuration register 1."]
    #[inline(always)]
    pub const fn bus_timing_1(&self) -> &BUS_TIMING_1 {
        &self.bus_timing_1
    }
    #[doc = "0x2c - TWAI arbiter lost capture register."]
    #[inline(always)]
    pub const fn arb_lost_cap(&self) -> &ARB_LOST_CAP {
        &self.arb_lost_cap
    }
    #[doc = "0x30 - TWAI error info capture register."]
    #[inline(always)]
    pub const fn err_code_cap(&self) -> &ERR_CODE_CAP {
        &self.err_code_cap
    }
    #[doc = "0x34 - TWAI error threshold configuration register."]
    #[inline(always)]
    pub const fn err_warning_limit(&self) -> &ERR_WARNING_LIMIT {
        &self.err_warning_limit
    }
    #[doc = "0x38 - Rx error counter register."]
    #[inline(always)]
    pub const fn rx_err_cnt(&self) -> &RX_ERR_CNT {
        &self.rx_err_cnt
    }
    #[doc = "0x3c - Tx error counter register."]
    #[inline(always)]
    pub const fn tx_err_cnt(&self) -> &TX_ERR_CNT {
        &self.tx_err_cnt
    }
    #[doc = "0x40..0x74 - Data register %s."]
    #[inline(always)]
    pub const fn data(&self, n: usize) -> &DATA {
        &self.data[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x40..0x74 - Data register %s."]
    #[inline(always)]
    pub fn data_iter(&self) -> impl Iterator<Item = &DATA> {
        self.data.iter()
    }
    #[doc = "0x74 - Received message counter register."]
    #[inline(always)]
    pub const fn rx_message_cnt(&self) -> &RX_MESSAGE_CNT {
        &self.rx_message_cnt
    }
    #[doc = "0x7c - Clock divider register."]
    #[inline(always)]
    pub const fn clock_divider(&self) -> &CLOCK_DIVIDER {
        &self.clock_divider
    }
    #[doc = "0x80 - Software configure standby pin directly."]
    #[inline(always)]
    pub const fn sw_standby_cfg(&self) -> &SW_STANDBY_CFG {
        &self.sw_standby_cfg
    }
    #[doc = "0x84 - Hardware configure standby pin."]
    #[inline(always)]
    pub const fn hw_cfg(&self) -> &HW_CFG {
        &self.hw_cfg
    }
    #[doc = "0x88 - Configure standby counter."]
    #[inline(always)]
    pub const fn hw_standby_cnt(&self) -> &HW_STANDBY_CNT {
        &self.hw_standby_cnt
    }
    #[doc = "0x8c - Configure idle interrupt counter."]
    #[inline(always)]
    pub const fn idle_intr_cnt(&self) -> &IDLE_INTR_CNT {
        &self.idle_intr_cnt
    }
    #[doc = "0x90 - ECO configuration register."]
    #[inline(always)]
    pub const fn eco_cfg(&self) -> &ECO_CFG {
        &self.eco_cfg
    }
}
#[doc = "MODE (rw) register accessor: TWAI mode register.\n\nYou can [`read`](crate::Reg::read) this register and get [`mode::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mode::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mode`] module"]
pub type MODE = crate::Reg<mode::MODE_SPEC>;
#[doc = "TWAI mode register."]
pub mod mode;
#[doc = "CMD (w) register accessor: TWAI command register.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cmd::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cmd`] module"]
pub type CMD = crate::Reg<cmd::CMD_SPEC>;
#[doc = "TWAI command register."]
pub mod cmd;
#[doc = "STATUS (r) register accessor: TWAI status register.\n\nYou can [`read`](crate::Reg::read) this register and get [`status::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@status`] module"]
pub type STATUS = crate::Reg<status::STATUS_SPEC>;
#[doc = "TWAI status register."]
pub mod status;
#[doc = "INT_RAW (r) register accessor: Interrupt signals' register.\n\nYou can [`read`](crate::Reg::read) this register and get [`int_raw::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_raw`] module"]
pub type INT_RAW = crate::Reg<int_raw::INT_RAW_SPEC>;
#[doc = "Interrupt signals' register."]
pub mod int_raw;
#[doc = "INT_ENA (rw) register accessor: Interrupt enable register.\n\nYou can [`read`](crate::Reg::read) this register and get [`int_ena::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_ena::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_ena`] module"]
pub type INT_ENA = crate::Reg<int_ena::INT_ENA_SPEC>;
#[doc = "Interrupt enable register."]
pub mod int_ena;
#[doc = "BUS_TIMING_0 (rw) register accessor: Bit timing configuration register 0.\n\nYou can [`read`](crate::Reg::read) this register and get [`bus_timing_0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`bus_timing_0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@bus_timing_0`] module"]
pub type BUS_TIMING_0 = crate::Reg<bus_timing_0::BUS_TIMING_0_SPEC>;
#[doc = "Bit timing configuration register 0."]
pub mod bus_timing_0;
#[doc = "BUS_TIMING_1 (rw) register accessor: Bit timing configuration register 1.\n\nYou can [`read`](crate::Reg::read) this register and get [`bus_timing_1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`bus_timing_1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@bus_timing_1`] module"]
pub type BUS_TIMING_1 = crate::Reg<bus_timing_1::BUS_TIMING_1_SPEC>;
#[doc = "Bit timing configuration register 1."]
pub mod bus_timing_1;
#[doc = "ARB_LOST_CAP (r) register accessor: TWAI arbiter lost capture register.\n\nYou can [`read`](crate::Reg::read) this register and get [`arb_lost_cap::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@arb_lost_cap`] module"]
pub type ARB_LOST_CAP = crate::Reg<arb_lost_cap::ARB_LOST_CAP_SPEC>;
#[doc = "TWAI arbiter lost capture register."]
pub mod arb_lost_cap;
#[doc = "ERR_CODE_CAP (r) register accessor: TWAI error info capture register.\n\nYou can [`read`](crate::Reg::read) this register and get [`err_code_cap::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@err_code_cap`] module"]
pub type ERR_CODE_CAP = crate::Reg<err_code_cap::ERR_CODE_CAP_SPEC>;
#[doc = "TWAI error info capture register."]
pub mod err_code_cap;
#[doc = "ERR_WARNING_LIMIT (rw) register accessor: TWAI error threshold configuration register.\n\nYou can [`read`](crate::Reg::read) this register and get [`err_warning_limit::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`err_warning_limit::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@err_warning_limit`] module"]
pub type ERR_WARNING_LIMIT = crate::Reg<err_warning_limit::ERR_WARNING_LIMIT_SPEC>;
#[doc = "TWAI error threshold configuration register."]
pub mod err_warning_limit;
#[doc = "RX_ERR_CNT (rw) register accessor: Rx error counter register.\n\nYou can [`read`](crate::Reg::read) this register and get [`rx_err_cnt::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rx_err_cnt::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rx_err_cnt`] module"]
pub type RX_ERR_CNT = crate::Reg<rx_err_cnt::RX_ERR_CNT_SPEC>;
#[doc = "Rx error counter register."]
pub mod rx_err_cnt;
#[doc = "TX_ERR_CNT (rw) register accessor: Tx error counter register.\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_err_cnt::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_err_cnt::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tx_err_cnt`] module"]
pub type TX_ERR_CNT = crate::Reg<tx_err_cnt::TX_ERR_CNT_SPEC>;
#[doc = "Tx error counter register."]
pub mod tx_err_cnt;
#[doc = "DATA (rw) register accessor: Data register %s.\n\nYou can [`read`](crate::Reg::read) this register and get [`data::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`data::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@data`] module"]
pub type DATA = crate::Reg<data::DATA_SPEC>;
#[doc = "Data register %s."]
pub mod data;
#[doc = "RX_MESSAGE_CNT (r) register accessor: Received message counter register.\n\nYou can [`read`](crate::Reg::read) this register and get [`rx_message_cnt::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rx_message_cnt`] module"]
pub type RX_MESSAGE_CNT = crate::Reg<rx_message_cnt::RX_MESSAGE_CNT_SPEC>;
#[doc = "Received message counter register."]
pub mod rx_message_cnt;
#[doc = "CLOCK_DIVIDER (rw) register accessor: Clock divider register.\n\nYou can [`read`](crate::Reg::read) this register and get [`clock_divider::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clock_divider::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@clock_divider`] module"]
pub type CLOCK_DIVIDER = crate::Reg<clock_divider::CLOCK_DIVIDER_SPEC>;
#[doc = "Clock divider register."]
pub mod clock_divider;
#[doc = "SW_STANDBY_CFG (rw) register accessor: Software configure standby pin directly.\n\nYou can [`read`](crate::Reg::read) this register and get [`sw_standby_cfg::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sw_standby_cfg::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sw_standby_cfg`] module"]
pub type SW_STANDBY_CFG = crate::Reg<sw_standby_cfg::SW_STANDBY_CFG_SPEC>;
#[doc = "Software configure standby pin directly."]
pub mod sw_standby_cfg;
#[doc = "HW_CFG (rw) register accessor: Hardware configure standby pin.\n\nYou can [`read`](crate::Reg::read) this register and get [`hw_cfg::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`hw_cfg::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hw_cfg`] module"]
pub type HW_CFG = crate::Reg<hw_cfg::HW_CFG_SPEC>;
#[doc = "Hardware configure standby pin."]
pub mod hw_cfg;
#[doc = "HW_STANDBY_CNT (rw) register accessor: Configure standby counter.\n\nYou can [`read`](crate::Reg::read) this register and get [`hw_standby_cnt::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`hw_standby_cnt::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hw_standby_cnt`] module"]
pub type HW_STANDBY_CNT = crate::Reg<hw_standby_cnt::HW_STANDBY_CNT_SPEC>;
#[doc = "Configure standby counter."]
pub mod hw_standby_cnt;
#[doc = "IDLE_INTR_CNT (rw) register accessor: Configure idle interrupt counter.\n\nYou can [`read`](crate::Reg::read) this register and get [`idle_intr_cnt::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`idle_intr_cnt::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@idle_intr_cnt`] module"]
pub type IDLE_INTR_CNT = crate::Reg<idle_intr_cnt::IDLE_INTR_CNT_SPEC>;
#[doc = "Configure idle interrupt counter."]
pub mod idle_intr_cnt;
#[doc = "ECO_CFG (rw) register accessor: ECO configuration register.\n\nYou can [`read`](crate::Reg::read) this register and get [`eco_cfg::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`eco_cfg::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@eco_cfg`] module"]
pub type ECO_CFG = crate::Reg<eco_cfg::ECO_CFG_SPEC>;
#[doc = "ECO configuration register."]
pub mod eco_cfg;
