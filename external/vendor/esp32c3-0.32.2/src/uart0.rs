#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    fifo: FIFO,
    int_raw: INT_RAW,
    int_st: INT_ST,
    int_ena: INT_ENA,
    int_clr: INT_CLR,
    clkdiv: CLKDIV,
    rx_filt: RX_FILT,
    status: STATUS,
    conf0: CONF0,
    conf1: CONF1,
    lowpulse: LOWPULSE,
    highpulse: HIGHPULSE,
    rxd_cnt: RXD_CNT,
    flow_conf: FLOW_CONF,
    sleep_conf: SLEEP_CONF,
    swfc_conf0: SWFC_CONF0,
    swfc_conf1: SWFC_CONF1,
    txbrk_conf: TXBRK_CONF,
    idle_conf: IDLE_CONF,
    rs485_conf: RS485_CONF,
    at_cmd_precnt: AT_CMD_PRECNT,
    at_cmd_postcnt: AT_CMD_POSTCNT,
    at_cmd_gaptout: AT_CMD_GAPTOUT,
    at_cmd_char: AT_CMD_CHAR,
    mem_conf: MEM_CONF,
    mem_tx_status: MEM_TX_STATUS,
    mem_rx_status: MEM_RX_STATUS,
    fsm_status: FSM_STATUS,
    pospulse: POSPULSE,
    negpulse: NEGPULSE,
    clk_conf: CLK_CONF,
    date: DATE,
    id: ID,
}
impl RegisterBlock {
    #[doc = "0x00 - FIFO data register"]
    #[inline(always)]
    pub const fn fifo(&self) -> &FIFO {
        &self.fifo
    }
    #[doc = "0x04 - Raw interrupt status"]
    #[inline(always)]
    pub const fn int_raw(&self) -> &INT_RAW {
        &self.int_raw
    }
    #[doc = "0x08 - Masked interrupt status"]
    #[inline(always)]
    pub const fn int_st(&self) -> &INT_ST {
        &self.int_st
    }
    #[doc = "0x0c - Interrupt enable bits"]
    #[inline(always)]
    pub const fn int_ena(&self) -> &INT_ENA {
        &self.int_ena
    }
    #[doc = "0x10 - Interrupt clear bits"]
    #[inline(always)]
    pub const fn int_clr(&self) -> &INT_CLR {
        &self.int_clr
    }
    #[doc = "0x14 - Clock divider configuration"]
    #[inline(always)]
    pub const fn clkdiv(&self) -> &CLKDIV {
        &self.clkdiv
    }
    #[doc = "0x18 - Rx Filter configuration"]
    #[inline(always)]
    pub const fn rx_filt(&self) -> &RX_FILT {
        &self.rx_filt
    }
    #[doc = "0x1c - UART status register"]
    #[inline(always)]
    pub const fn status(&self) -> &STATUS {
        &self.status
    }
    #[doc = "0x20 - a"]
    #[inline(always)]
    pub const fn conf0(&self) -> &CONF0 {
        &self.conf0
    }
    #[doc = "0x24 - Configuration register 1"]
    #[inline(always)]
    pub const fn conf1(&self) -> &CONF1 {
        &self.conf1
    }
    #[doc = "0x28 - Autobaud minimum low pulse duration register"]
    #[inline(always)]
    pub const fn lowpulse(&self) -> &LOWPULSE {
        &self.lowpulse
    }
    #[doc = "0x2c - Autobaud minimum high pulse duration register"]
    #[inline(always)]
    pub const fn highpulse(&self) -> &HIGHPULSE {
        &self.highpulse
    }
    #[doc = "0x30 - Autobaud edge change count register"]
    #[inline(always)]
    pub const fn rxd_cnt(&self) -> &RXD_CNT {
        &self.rxd_cnt
    }
    #[doc = "0x34 - Software flow-control configuration"]
    #[inline(always)]
    pub const fn flow_conf(&self) -> &FLOW_CONF {
        &self.flow_conf
    }
    #[doc = "0x38 - Sleep-mode configuration"]
    #[inline(always)]
    pub const fn sleep_conf(&self) -> &SLEEP_CONF {
        &self.sleep_conf
    }
    #[doc = "0x3c - Software flow-control character configuration"]
    #[inline(always)]
    pub const fn swfc_conf0(&self) -> &SWFC_CONF0 {
        &self.swfc_conf0
    }
    #[doc = "0x40 - Software flow-control character configuration"]
    #[inline(always)]
    pub const fn swfc_conf1(&self) -> &SWFC_CONF1 {
        &self.swfc_conf1
    }
    #[doc = "0x44 - Tx Break character configuration"]
    #[inline(always)]
    pub const fn txbrk_conf(&self) -> &TXBRK_CONF {
        &self.txbrk_conf
    }
    #[doc = "0x48 - Frame-end idle configuration"]
    #[inline(always)]
    pub const fn idle_conf(&self) -> &IDLE_CONF {
        &self.idle_conf
    }
    #[doc = "0x4c - RS485 mode configuration"]
    #[inline(always)]
    pub const fn rs485_conf(&self) -> &RS485_CONF {
        &self.rs485_conf
    }
    #[doc = "0x50 - Pre-sequence timing configuration"]
    #[inline(always)]
    pub const fn at_cmd_precnt(&self) -> &AT_CMD_PRECNT {
        &self.at_cmd_precnt
    }
    #[doc = "0x54 - Post-sequence timing configuration"]
    #[inline(always)]
    pub const fn at_cmd_postcnt(&self) -> &AT_CMD_POSTCNT {
        &self.at_cmd_postcnt
    }
    #[doc = "0x58 - Timeout configuration"]
    #[inline(always)]
    pub const fn at_cmd_gaptout(&self) -> &AT_CMD_GAPTOUT {
        &self.at_cmd_gaptout
    }
    #[doc = "0x5c - AT escape sequence detection configuration"]
    #[inline(always)]
    pub const fn at_cmd_char(&self) -> &AT_CMD_CHAR {
        &self.at_cmd_char
    }
    #[doc = "0x60 - UART threshold and allocation configuration"]
    #[inline(always)]
    pub const fn mem_conf(&self) -> &MEM_CONF {
        &self.mem_conf
    }
    #[doc = "0x64 - Tx-FIFO write and read offset address."]
    #[inline(always)]
    pub const fn mem_tx_status(&self) -> &MEM_TX_STATUS {
        &self.mem_tx_status
    }
    #[doc = "0x68 - Rx-FIFO write and read offset address."]
    #[inline(always)]
    pub const fn mem_rx_status(&self) -> &MEM_RX_STATUS {
        &self.mem_rx_status
    }
    #[doc = "0x6c - UART transmit and receive status."]
    #[inline(always)]
    pub const fn fsm_status(&self) -> &FSM_STATUS {
        &self.fsm_status
    }
    #[doc = "0x70 - Autobaud high pulse register"]
    #[inline(always)]
    pub const fn pospulse(&self) -> &POSPULSE {
        &self.pospulse
    }
    #[doc = "0x74 - Autobaud low pulse register"]
    #[inline(always)]
    pub const fn negpulse(&self) -> &NEGPULSE {
        &self.negpulse
    }
    #[doc = "0x78 - UART core clock configuration"]
    #[inline(always)]
    pub const fn clk_conf(&self) -> &CLK_CONF {
        &self.clk_conf
    }
    #[doc = "0x7c - UART Version register"]
    #[inline(always)]
    pub const fn date(&self) -> &DATE {
        &self.date
    }
    #[doc = "0x80 - UART ID register"]
    #[inline(always)]
    pub const fn id(&self) -> &ID {
        &self.id
    }
}
#[doc = "FIFO (rw) register accessor: FIFO data register\n\nYou can [`read`](crate::Reg::read) this register and get [`fifo::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`fifo::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@fifo`] module"]
pub type FIFO = crate::Reg<fifo::FIFO_SPEC>;
#[doc = "FIFO data register"]
pub mod fifo;
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
#[doc = "CLKDIV (rw) register accessor: Clock divider configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`clkdiv::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clkdiv::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@clkdiv`] module"]
pub type CLKDIV = crate::Reg<clkdiv::CLKDIV_SPEC>;
#[doc = "Clock divider configuration"]
pub mod clkdiv;
#[doc = "RX_FILT (rw) register accessor: Rx Filter configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`rx_filt::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rx_filt::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rx_filt`] module"]
pub type RX_FILT = crate::Reg<rx_filt::RX_FILT_SPEC>;
#[doc = "Rx Filter configuration"]
pub mod rx_filt;
#[doc = "STATUS (r) register accessor: UART status register\n\nYou can [`read`](crate::Reg::read) this register and get [`status::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@status`] module"]
pub type STATUS = crate::Reg<status::STATUS_SPEC>;
#[doc = "UART status register"]
pub mod status;
#[doc = "CONF0 (rw) register accessor: a\n\nYou can [`read`](crate::Reg::read) this register and get [`conf0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@conf0`] module"]
pub type CONF0 = crate::Reg<conf0::CONF0_SPEC>;
#[doc = "a"]
pub mod conf0;
#[doc = "CONF1 (rw) register accessor: Configuration register 1\n\nYou can [`read`](crate::Reg::read) this register and get [`conf1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@conf1`] module"]
pub type CONF1 = crate::Reg<conf1::CONF1_SPEC>;
#[doc = "Configuration register 1"]
pub mod conf1;
#[doc = "LOWPULSE (r) register accessor: Autobaud minimum low pulse duration register\n\nYou can [`read`](crate::Reg::read) this register and get [`lowpulse::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@lowpulse`] module"]
pub type LOWPULSE = crate::Reg<lowpulse::LOWPULSE_SPEC>;
#[doc = "Autobaud minimum low pulse duration register"]
pub mod lowpulse;
#[doc = "HIGHPULSE (r) register accessor: Autobaud minimum high pulse duration register\n\nYou can [`read`](crate::Reg::read) this register and get [`highpulse::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@highpulse`] module"]
pub type HIGHPULSE = crate::Reg<highpulse::HIGHPULSE_SPEC>;
#[doc = "Autobaud minimum high pulse duration register"]
pub mod highpulse;
#[doc = "RXD_CNT (r) register accessor: Autobaud edge change count register\n\nYou can [`read`](crate::Reg::read) this register and get [`rxd_cnt::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rxd_cnt`] module"]
pub type RXD_CNT = crate::Reg<rxd_cnt::RXD_CNT_SPEC>;
#[doc = "Autobaud edge change count register"]
pub mod rxd_cnt;
#[doc = "FLOW_CONF (rw) register accessor: Software flow-control configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`flow_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`flow_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@flow_conf`] module"]
pub type FLOW_CONF = crate::Reg<flow_conf::FLOW_CONF_SPEC>;
#[doc = "Software flow-control configuration"]
pub mod flow_conf;
#[doc = "SLEEP_CONF (rw) register accessor: Sleep-mode configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`sleep_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sleep_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sleep_conf`] module"]
pub type SLEEP_CONF = crate::Reg<sleep_conf::SLEEP_CONF_SPEC>;
#[doc = "Sleep-mode configuration"]
pub mod sleep_conf;
#[doc = "SWFC_CONF0 (rw) register accessor: Software flow-control character configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`swfc_conf0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`swfc_conf0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@swfc_conf0`] module"]
pub type SWFC_CONF0 = crate::Reg<swfc_conf0::SWFC_CONF0_SPEC>;
#[doc = "Software flow-control character configuration"]
pub mod swfc_conf0;
#[doc = "SWFC_CONF1 (rw) register accessor: Software flow-control character configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`swfc_conf1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`swfc_conf1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@swfc_conf1`] module"]
pub type SWFC_CONF1 = crate::Reg<swfc_conf1::SWFC_CONF1_SPEC>;
#[doc = "Software flow-control character configuration"]
pub mod swfc_conf1;
#[doc = "TXBRK_CONF (rw) register accessor: Tx Break character configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`txbrk_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`txbrk_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@txbrk_conf`] module"]
pub type TXBRK_CONF = crate::Reg<txbrk_conf::TXBRK_CONF_SPEC>;
#[doc = "Tx Break character configuration"]
pub mod txbrk_conf;
#[doc = "IDLE_CONF (rw) register accessor: Frame-end idle configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`idle_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`idle_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@idle_conf`] module"]
pub type IDLE_CONF = crate::Reg<idle_conf::IDLE_CONF_SPEC>;
#[doc = "Frame-end idle configuration"]
pub mod idle_conf;
#[doc = "RS485_CONF (rw) register accessor: RS485 mode configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`rs485_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rs485_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rs485_conf`] module"]
pub type RS485_CONF = crate::Reg<rs485_conf::RS485_CONF_SPEC>;
#[doc = "RS485 mode configuration"]
pub mod rs485_conf;
#[doc = "AT_CMD_PRECNT (rw) register accessor: Pre-sequence timing configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`at_cmd_precnt::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`at_cmd_precnt::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@at_cmd_precnt`] module"]
pub type AT_CMD_PRECNT = crate::Reg<at_cmd_precnt::AT_CMD_PRECNT_SPEC>;
#[doc = "Pre-sequence timing configuration"]
pub mod at_cmd_precnt;
#[doc = "AT_CMD_POSTCNT (rw) register accessor: Post-sequence timing configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`at_cmd_postcnt::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`at_cmd_postcnt::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@at_cmd_postcnt`] module"]
pub type AT_CMD_POSTCNT = crate::Reg<at_cmd_postcnt::AT_CMD_POSTCNT_SPEC>;
#[doc = "Post-sequence timing configuration"]
pub mod at_cmd_postcnt;
#[doc = "AT_CMD_GAPTOUT (rw) register accessor: Timeout configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`at_cmd_gaptout::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`at_cmd_gaptout::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@at_cmd_gaptout`] module"]
pub type AT_CMD_GAPTOUT = crate::Reg<at_cmd_gaptout::AT_CMD_GAPTOUT_SPEC>;
#[doc = "Timeout configuration"]
pub mod at_cmd_gaptout;
#[doc = "AT_CMD_CHAR (rw) register accessor: AT escape sequence detection configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`at_cmd_char::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`at_cmd_char::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@at_cmd_char`] module"]
pub type AT_CMD_CHAR = crate::Reg<at_cmd_char::AT_CMD_CHAR_SPEC>;
#[doc = "AT escape sequence detection configuration"]
pub mod at_cmd_char;
#[doc = "MEM_CONF (rw) register accessor: UART threshold and allocation configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`mem_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mem_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mem_conf`] module"]
pub type MEM_CONF = crate::Reg<mem_conf::MEM_CONF_SPEC>;
#[doc = "UART threshold and allocation configuration"]
pub mod mem_conf;
#[doc = "MEM_TX_STATUS (r) register accessor: Tx-FIFO write and read offset address.\n\nYou can [`read`](crate::Reg::read) this register and get [`mem_tx_status::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mem_tx_status`] module"]
pub type MEM_TX_STATUS = crate::Reg<mem_tx_status::MEM_TX_STATUS_SPEC>;
#[doc = "Tx-FIFO write and read offset address."]
pub mod mem_tx_status;
#[doc = "MEM_RX_STATUS (r) register accessor: Rx-FIFO write and read offset address.\n\nYou can [`read`](crate::Reg::read) this register and get [`mem_rx_status::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mem_rx_status`] module"]
pub type MEM_RX_STATUS = crate::Reg<mem_rx_status::MEM_RX_STATUS_SPEC>;
#[doc = "Rx-FIFO write and read offset address."]
pub mod mem_rx_status;
#[doc = "FSM_STATUS (r) register accessor: UART transmit and receive status.\n\nYou can [`read`](crate::Reg::read) this register and get [`fsm_status::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@fsm_status`] module"]
pub type FSM_STATUS = crate::Reg<fsm_status::FSM_STATUS_SPEC>;
#[doc = "UART transmit and receive status."]
pub mod fsm_status;
#[doc = "POSPULSE (r) register accessor: Autobaud high pulse register\n\nYou can [`read`](crate::Reg::read) this register and get [`pospulse::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pospulse`] module"]
pub type POSPULSE = crate::Reg<pospulse::POSPULSE_SPEC>;
#[doc = "Autobaud high pulse register"]
pub mod pospulse;
#[doc = "NEGPULSE (r) register accessor: Autobaud low pulse register\n\nYou can [`read`](crate::Reg::read) this register and get [`negpulse::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@negpulse`] module"]
pub type NEGPULSE = crate::Reg<negpulse::NEGPULSE_SPEC>;
#[doc = "Autobaud low pulse register"]
pub mod negpulse;
#[doc = "CLK_CONF (rw) register accessor: UART core clock configuration\n\nYou can [`read`](crate::Reg::read) this register and get [`clk_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clk_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@clk_conf`] module"]
pub type CLK_CONF = crate::Reg<clk_conf::CLK_CONF_SPEC>;
#[doc = "UART core clock configuration"]
pub mod clk_conf;
pub use crate::aes::{date, DATE};
#[doc = "ID (rw) register accessor: UART ID register\n\nYou can [`read`](crate::Reg::read) this register and get [`id::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`id::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@id`] module"]
pub type ID = crate::Reg<id::ID_SPEC>;
#[doc = "UART ID register"]
pub mod id;
