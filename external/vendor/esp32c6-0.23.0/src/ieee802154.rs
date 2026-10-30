#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    command: COMMAND,
    ctrl_cfg: CTRL_CFG,
    inf: [INF; 4],
    channel: CHANNEL,
    tx_power: TX_POWER,
    ed_scan_duration: ED_SCAN_DURATION,
    ed_scan_cfg: ED_SCAN_CFG,
    ifs: IFS,
    ack_timeout: ACK_TIMEOUT,
    event_en: EVENT_EN,
    event_status: EVENT_STATUS,
    rx_abort_intr_ctrl: RX_ABORT_INTR_CTRL,
    ack_frame_pending_en: ACK_FRAME_PENDING_EN,
    coex_pti: COEX_PTI,
    core_dummy_data: CORE_DUMMY_DATA,
    tx_abort_interrupt_control: TX_ABORT_INTERRUPT_CONTROL,
    enhance_ack_cfg: ENHANCE_ACK_CFG,
    rx_status: RX_STATUS,
    tx_status: TX_STATUS,
    txrx_status: TXRX_STATUS,
    tx_ccm_schedule_status: TX_CCM_SCHEDULE_STATUS,
    core_gck_cfg: CORE_GCK_CFG,
    test_control: TEST_CONTROL,
    dtm_config: DTM_CONFIG,
    dtm_tx_pkt_config: DTM_TX_PKT_CONFIG,
    dtm_pkt_counter: DTM_PKT_COUNTER,
    rx_length: RX_LENGTH,
    time: [TIME; 2],
    clk_counter_match_val: CLK_COUNTER_MATCH_VAL,
    clk_counter: CLK_COUNTER,
    ifs_counter: IFS_COUNTER,
    sfd_wait_symbol: SFD_WAIT_SYMBOL,
    txrx_path_delay: TXRX_PATH_DELAY,
    bb_clk: BB_CLK,
    txdma_addr: TXDMA_ADDR,
    txdma_ctrl_state: TXDMA_CTRL_STATE,
    txdma_err: TXDMA_ERR,
    _reserved37: [u8; 0x04],
    rxdma_addr: RXDMA_ADDR,
    rxdma_ctrl_state: RXDMA_CTRL_STATE,
    rxdma_err: RXDMA_ERR,
    _reserved40: [u8; 0x04],
    dma_gck_cfg: DMA_GCK_CFG,
    dma_dummy: DMA_DUMMY,
    _reserved42: [u8; 0x08],
    paon_delay: PAON_DELAY,
    txon_delay: TXON_DELAY,
    txen_stop_delay: TXEN_STOP_DELAY,
    txoff_delay: TXOFF_DELAY,
    rxon_delay: RXON_DELAY,
    txrx_switch_delay: TXRX_SWITCH_DELAY,
    cont_rx_delay: CONT_RX_DELAY,
    dcdc_ctrl: DCDC_CTRL,
    debug_ctrl: DEBUG_CTRL,
    _reserved51: [u8; 0x04],
    sec_ctrl: SEC_CTRL,
    sec_extend_address0: SEC_EXTEND_ADDRESS0,
    sec_extend_address1: SEC_EXTEND_ADDRESS1,
    sec_key: [SEC_KEY; 4],
    sfd_timeout_cnt: SFD_TIMEOUT_CNT,
    crc_error_cnt: CRC_ERROR_CNT,
    ed_abort_cnt: ED_ABORT_CNT,
    cca_fail_cnt: CCA_FAIL_CNT,
    rx_filter_fail_cnt: RX_FILTER_FAIL_CNT,
    no_rss_detect_cnt: NO_RSS_DETECT_CNT,
    rx_abort_coex_cnt: RX_ABORT_COEX_CNT,
    rx_restart_cnt: RX_RESTART_CNT,
    tx_ack_abort_coex_cnt: TX_ACK_ABORT_COEX_CNT,
    ed_scan_coex_cnt: ED_SCAN_COEX_CNT,
    rx_ack_abort_coex_cnt: RX_ACK_ABORT_COEX_CNT,
    rx_ack_timeout_cnt: RX_ACK_TIMEOUT_CNT,
    tx_break_coex_cnt: TX_BREAK_COEX_CNT,
    tx_security_error_cnt: TX_SECURITY_ERROR_CNT,
    cca_busy_cnt: CCA_BUSY_CNT,
    error_cnt_clear: ERROR_CNT_CLEAR,
    mac_date: MAC_DATE,
}
impl RegisterBlock {
    #[doc = "0x00 - "]
    #[inline(always)]
    pub const fn command(&self) -> &COMMAND {
        &self.command
    }
    #[doc = "0x04 - "]
    #[inline(always)]
    pub const fn ctrl_cfg(&self) -> &CTRL_CFG {
        &self.ctrl_cfg
    }
    #[doc = "0x08..0x48 - Cluster INF%s, containing INF?_EXTEND_ADDR0, INF?_EXTEND_ADDR1, INF?_PAN_ID, INF?_SHORT_ADDR"]
    #[inline(always)]
    pub const fn inf(&self, n: usize) -> &INF {
        &self.inf[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x08..0x48 - Cluster INF%s, containing INF?_EXTEND_ADDR0, INF?_EXTEND_ADDR1, INF?_PAN_ID, INF?_SHORT_ADDR"]
    #[inline(always)]
    pub fn inf_iter(&self) -> impl Iterator<Item = &INF> {
        self.inf.iter()
    }
    #[doc = "0x48 - "]
    #[inline(always)]
    pub const fn channel(&self) -> &CHANNEL {
        &self.channel
    }
    #[doc = "0x4c - "]
    #[inline(always)]
    pub const fn tx_power(&self) -> &TX_POWER {
        &self.tx_power
    }
    #[doc = "0x50 - "]
    #[inline(always)]
    pub const fn ed_scan_duration(&self) -> &ED_SCAN_DURATION {
        &self.ed_scan_duration
    }
    #[doc = "0x54 - "]
    #[inline(always)]
    pub const fn ed_scan_cfg(&self) -> &ED_SCAN_CFG {
        &self.ed_scan_cfg
    }
    #[doc = "0x58 - "]
    #[inline(always)]
    pub const fn ifs(&self) -> &IFS {
        &self.ifs
    }
    #[doc = "0x5c - "]
    #[inline(always)]
    pub const fn ack_timeout(&self) -> &ACK_TIMEOUT {
        &self.ack_timeout
    }
    #[doc = "0x60 - "]
    #[inline(always)]
    pub const fn event_en(&self) -> &EVENT_EN {
        &self.event_en
    }
    #[doc = "0x64 - "]
    #[inline(always)]
    pub const fn event_status(&self) -> &EVENT_STATUS {
        &self.event_status
    }
    #[doc = "0x68 - "]
    #[inline(always)]
    pub const fn rx_abort_intr_ctrl(&self) -> &RX_ABORT_INTR_CTRL {
        &self.rx_abort_intr_ctrl
    }
    #[doc = "0x6c - "]
    #[inline(always)]
    pub const fn ack_frame_pending_en(&self) -> &ACK_FRAME_PENDING_EN {
        &self.ack_frame_pending_en
    }
    #[doc = "0x70 - "]
    #[inline(always)]
    pub const fn coex_pti(&self) -> &COEX_PTI {
        &self.coex_pti
    }
    #[doc = "0x74 - "]
    #[inline(always)]
    pub const fn core_dummy_data(&self) -> &CORE_DUMMY_DATA {
        &self.core_dummy_data
    }
    #[doc = "0x78 - "]
    #[inline(always)]
    pub const fn tx_abort_interrupt_control(&self) -> &TX_ABORT_INTERRUPT_CONTROL {
        &self.tx_abort_interrupt_control
    }
    #[doc = "0x7c - "]
    #[inline(always)]
    pub const fn enhance_ack_cfg(&self) -> &ENHANCE_ACK_CFG {
        &self.enhance_ack_cfg
    }
    #[doc = "0x80 - "]
    #[inline(always)]
    pub const fn rx_status(&self) -> &RX_STATUS {
        &self.rx_status
    }
    #[doc = "0x84 - "]
    #[inline(always)]
    pub const fn tx_status(&self) -> &TX_STATUS {
        &self.tx_status
    }
    #[doc = "0x88 - "]
    #[inline(always)]
    pub const fn txrx_status(&self) -> &TXRX_STATUS {
        &self.txrx_status
    }
    #[doc = "0x8c - "]
    #[inline(always)]
    pub const fn tx_ccm_schedule_status(&self) -> &TX_CCM_SCHEDULE_STATUS {
        &self.tx_ccm_schedule_status
    }
    #[doc = "0x90 - "]
    #[inline(always)]
    pub const fn core_gck_cfg(&self) -> &CORE_GCK_CFG {
        &self.core_gck_cfg
    }
    #[doc = "0x94 - "]
    #[inline(always)]
    pub const fn test_control(&self) -> &TEST_CONTROL {
        &self.test_control
    }
    #[doc = "0x98 - "]
    #[inline(always)]
    pub const fn dtm_config(&self) -> &DTM_CONFIG {
        &self.dtm_config
    }
    #[doc = "0x9c - "]
    #[inline(always)]
    pub const fn dtm_tx_pkt_config(&self) -> &DTM_TX_PKT_CONFIG {
        &self.dtm_tx_pkt_config
    }
    #[doc = "0xa0 - "]
    #[inline(always)]
    pub const fn dtm_pkt_counter(&self) -> &DTM_PKT_COUNTER {
        &self.dtm_pkt_counter
    }
    #[doc = "0xa4 - "]
    #[inline(always)]
    pub const fn rx_length(&self) -> &RX_LENGTH {
        &self.rx_length
    }
    #[doc = "0xa8..0xb8 - Cluster TIME%s, containing TIME?_THRESHOLD, TIME?_VALUE"]
    #[inline(always)]
    pub const fn time(&self, n: usize) -> &TIME {
        &self.time[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0xa8..0xb8 - Cluster TIME%s, containing TIME?_THRESHOLD, TIME?_VALUE"]
    #[inline(always)]
    pub fn time_iter(&self) -> impl Iterator<Item = &TIME> {
        self.time.iter()
    }
    #[doc = "0xb8 - "]
    #[inline(always)]
    pub const fn clk_counter_match_val(&self) -> &CLK_COUNTER_MATCH_VAL {
        &self.clk_counter_match_val
    }
    #[doc = "0xbc - "]
    #[inline(always)]
    pub const fn clk_counter(&self) -> &CLK_COUNTER {
        &self.clk_counter
    }
    #[doc = "0xc0 - "]
    #[inline(always)]
    pub const fn ifs_counter(&self) -> &IFS_COUNTER {
        &self.ifs_counter
    }
    #[doc = "0xc4 - "]
    #[inline(always)]
    pub const fn sfd_wait_symbol(&self) -> &SFD_WAIT_SYMBOL {
        &self.sfd_wait_symbol
    }
    #[doc = "0xc8 - "]
    #[inline(always)]
    pub const fn txrx_path_delay(&self) -> &TXRX_PATH_DELAY {
        &self.txrx_path_delay
    }
    #[doc = "0xcc - "]
    #[inline(always)]
    pub const fn bb_clk(&self) -> &BB_CLK {
        &self.bb_clk
    }
    #[doc = "0xd0 - "]
    #[inline(always)]
    pub const fn txdma_addr(&self) -> &TXDMA_ADDR {
        &self.txdma_addr
    }
    #[doc = "0xd4 - "]
    #[inline(always)]
    pub const fn txdma_ctrl_state(&self) -> &TXDMA_CTRL_STATE {
        &self.txdma_ctrl_state
    }
    #[doc = "0xd8 - "]
    #[inline(always)]
    pub const fn txdma_err(&self) -> &TXDMA_ERR {
        &self.txdma_err
    }
    #[doc = "0xe0 - "]
    #[inline(always)]
    pub const fn rxdma_addr(&self) -> &RXDMA_ADDR {
        &self.rxdma_addr
    }
    #[doc = "0xe4 - "]
    #[inline(always)]
    pub const fn rxdma_ctrl_state(&self) -> &RXDMA_CTRL_STATE {
        &self.rxdma_ctrl_state
    }
    #[doc = "0xe8 - "]
    #[inline(always)]
    pub const fn rxdma_err(&self) -> &RXDMA_ERR {
        &self.rxdma_err
    }
    #[doc = "0xf0 - "]
    #[inline(always)]
    pub const fn dma_gck_cfg(&self) -> &DMA_GCK_CFG {
        &self.dma_gck_cfg
    }
    #[doc = "0xf4 - "]
    #[inline(always)]
    pub const fn dma_dummy(&self) -> &DMA_DUMMY {
        &self.dma_dummy
    }
    #[doc = "0x100 - "]
    #[inline(always)]
    pub const fn paon_delay(&self) -> &PAON_DELAY {
        &self.paon_delay
    }
    #[doc = "0x104 - "]
    #[inline(always)]
    pub const fn txon_delay(&self) -> &TXON_DELAY {
        &self.txon_delay
    }
    #[doc = "0x108 - "]
    #[inline(always)]
    pub const fn txen_stop_delay(&self) -> &TXEN_STOP_DELAY {
        &self.txen_stop_delay
    }
    #[doc = "0x10c - "]
    #[inline(always)]
    pub const fn txoff_delay(&self) -> &TXOFF_DELAY {
        &self.txoff_delay
    }
    #[doc = "0x110 - "]
    #[inline(always)]
    pub const fn rxon_delay(&self) -> &RXON_DELAY {
        &self.rxon_delay
    }
    #[doc = "0x114 - "]
    #[inline(always)]
    pub const fn txrx_switch_delay(&self) -> &TXRX_SWITCH_DELAY {
        &self.txrx_switch_delay
    }
    #[doc = "0x118 - "]
    #[inline(always)]
    pub const fn cont_rx_delay(&self) -> &CONT_RX_DELAY {
        &self.cont_rx_delay
    }
    #[doc = "0x11c - "]
    #[inline(always)]
    pub const fn dcdc_ctrl(&self) -> &DCDC_CTRL {
        &self.dcdc_ctrl
    }
    #[doc = "0x120 - "]
    #[inline(always)]
    pub const fn debug_ctrl(&self) -> &DEBUG_CTRL {
        &self.debug_ctrl
    }
    #[doc = "0x128 - "]
    #[inline(always)]
    pub const fn sec_ctrl(&self) -> &SEC_CTRL {
        &self.sec_ctrl
    }
    #[doc = "0x12c - "]
    #[inline(always)]
    pub const fn sec_extend_address0(&self) -> &SEC_EXTEND_ADDRESS0 {
        &self.sec_extend_address0
    }
    #[doc = "0x130 - "]
    #[inline(always)]
    pub const fn sec_extend_address1(&self) -> &SEC_EXTEND_ADDRESS1 {
        &self.sec_extend_address1
    }
    #[doc = "0x134..0x144 - "]
    #[inline(always)]
    pub const fn sec_key(&self, n: usize) -> &SEC_KEY {
        &self.sec_key[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x134..0x144 - "]
    #[inline(always)]
    pub fn sec_key_iter(&self) -> impl Iterator<Item = &SEC_KEY> {
        self.sec_key.iter()
    }
    #[doc = "0x144 - "]
    #[inline(always)]
    pub const fn sfd_timeout_cnt(&self) -> &SFD_TIMEOUT_CNT {
        &self.sfd_timeout_cnt
    }
    #[doc = "0x148 - "]
    #[inline(always)]
    pub const fn crc_error_cnt(&self) -> &CRC_ERROR_CNT {
        &self.crc_error_cnt
    }
    #[doc = "0x14c - "]
    #[inline(always)]
    pub const fn ed_abort_cnt(&self) -> &ED_ABORT_CNT {
        &self.ed_abort_cnt
    }
    #[doc = "0x150 - "]
    #[inline(always)]
    pub const fn cca_fail_cnt(&self) -> &CCA_FAIL_CNT {
        &self.cca_fail_cnt
    }
    #[doc = "0x154 - "]
    #[inline(always)]
    pub const fn rx_filter_fail_cnt(&self) -> &RX_FILTER_FAIL_CNT {
        &self.rx_filter_fail_cnt
    }
    #[doc = "0x158 - "]
    #[inline(always)]
    pub const fn no_rss_detect_cnt(&self) -> &NO_RSS_DETECT_CNT {
        &self.no_rss_detect_cnt
    }
    #[doc = "0x15c - "]
    #[inline(always)]
    pub const fn rx_abort_coex_cnt(&self) -> &RX_ABORT_COEX_CNT {
        &self.rx_abort_coex_cnt
    }
    #[doc = "0x160 - "]
    #[inline(always)]
    pub const fn rx_restart_cnt(&self) -> &RX_RESTART_CNT {
        &self.rx_restart_cnt
    }
    #[doc = "0x164 - "]
    #[inline(always)]
    pub const fn tx_ack_abort_coex_cnt(&self) -> &TX_ACK_ABORT_COEX_CNT {
        &self.tx_ack_abort_coex_cnt
    }
    #[doc = "0x168 - "]
    #[inline(always)]
    pub const fn ed_scan_coex_cnt(&self) -> &ED_SCAN_COEX_CNT {
        &self.ed_scan_coex_cnt
    }
    #[doc = "0x16c - "]
    #[inline(always)]
    pub const fn rx_ack_abort_coex_cnt(&self) -> &RX_ACK_ABORT_COEX_CNT {
        &self.rx_ack_abort_coex_cnt
    }
    #[doc = "0x170 - "]
    #[inline(always)]
    pub const fn rx_ack_timeout_cnt(&self) -> &RX_ACK_TIMEOUT_CNT {
        &self.rx_ack_timeout_cnt
    }
    #[doc = "0x174 - "]
    #[inline(always)]
    pub const fn tx_break_coex_cnt(&self) -> &TX_BREAK_COEX_CNT {
        &self.tx_break_coex_cnt
    }
    #[doc = "0x178 - "]
    #[inline(always)]
    pub const fn tx_security_error_cnt(&self) -> &TX_SECURITY_ERROR_CNT {
        &self.tx_security_error_cnt
    }
    #[doc = "0x17c - "]
    #[inline(always)]
    pub const fn cca_busy_cnt(&self) -> &CCA_BUSY_CNT {
        &self.cca_busy_cnt
    }
    #[doc = "0x180 - "]
    #[inline(always)]
    pub const fn error_cnt_clear(&self) -> &ERROR_CNT_CLEAR {
        &self.error_cnt_clear
    }
    #[doc = "0x184 - AES version control register"]
    #[inline(always)]
    pub const fn mac_date(&self) -> &MAC_DATE {
        &self.mac_date
    }
}
#[doc = "COMMAND (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`command::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`command::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@command`] module"]
pub type COMMAND = crate::Reg<command::COMMAND_SPEC>;
#[doc = ""]
pub mod command;
#[doc = "CTRL_CFG (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`ctrl_cfg::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ctrl_cfg::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ctrl_cfg`] module"]
pub type CTRL_CFG = crate::Reg<ctrl_cfg::CTRL_CFG_SPEC>;
#[doc = ""]
pub mod ctrl_cfg;
#[doc = "Cluster INF%s, containing INF?_EXTEND_ADDR0, INF?_EXTEND_ADDR1, INF?_PAN_ID, INF?_SHORT_ADDR"]
pub use self::inf::INF;
#[doc = r"Cluster"]
#[doc = "Cluster INF%s, containing INF?_EXTEND_ADDR0, INF?_EXTEND_ADDR1, INF?_PAN_ID, INF?_SHORT_ADDR"]
pub mod inf;
#[doc = "CHANNEL (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`channel::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`channel::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@channel`] module"]
pub type CHANNEL = crate::Reg<channel::CHANNEL_SPEC>;
#[doc = ""]
pub mod channel;
#[doc = "TX_POWER (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`tx_power::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_power::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tx_power`] module"]
pub type TX_POWER = crate::Reg<tx_power::TX_POWER_SPEC>;
#[doc = ""]
pub mod tx_power;
#[doc = "ED_SCAN_DURATION (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`ed_scan_duration::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ed_scan_duration::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ed_scan_duration`] module"]
pub type ED_SCAN_DURATION = crate::Reg<ed_scan_duration::ED_SCAN_DURATION_SPEC>;
#[doc = ""]
pub mod ed_scan_duration;
#[doc = "ED_SCAN_CFG (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`ed_scan_cfg::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ed_scan_cfg::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ed_scan_cfg`] module"]
pub type ED_SCAN_CFG = crate::Reg<ed_scan_cfg::ED_SCAN_CFG_SPEC>;
#[doc = ""]
pub mod ed_scan_cfg;
#[doc = "IFS (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`ifs::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ifs::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ifs`] module"]
pub type IFS = crate::Reg<ifs::IFS_SPEC>;
#[doc = ""]
pub mod ifs;
#[doc = "ACK_TIMEOUT (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`ack_timeout::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ack_timeout::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ack_timeout`] module"]
pub type ACK_TIMEOUT = crate::Reg<ack_timeout::ACK_TIMEOUT_SPEC>;
#[doc = ""]
pub mod ack_timeout;
#[doc = "EVENT_EN (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`event_en::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`event_en::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@event_en`] module"]
pub type EVENT_EN = crate::Reg<event_en::EVENT_EN_SPEC>;
#[doc = ""]
pub mod event_en;
#[doc = "EVENT_STATUS (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`event_status::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`event_status::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@event_status`] module"]
pub type EVENT_STATUS = crate::Reg<event_status::EVENT_STATUS_SPEC>;
#[doc = ""]
pub mod event_status;
#[doc = "RX_ABORT_INTR_CTRL (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`rx_abort_intr_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rx_abort_intr_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rx_abort_intr_ctrl`] module"]
pub type RX_ABORT_INTR_CTRL = crate::Reg<rx_abort_intr_ctrl::RX_ABORT_INTR_CTRL_SPEC>;
#[doc = ""]
pub mod rx_abort_intr_ctrl;
#[doc = "ACK_FRAME_PENDING_EN (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`ack_frame_pending_en::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ack_frame_pending_en::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ack_frame_pending_en`] module"]
pub type ACK_FRAME_PENDING_EN = crate::Reg<ack_frame_pending_en::ACK_FRAME_PENDING_EN_SPEC>;
#[doc = ""]
pub mod ack_frame_pending_en;
#[doc = "COEX_PTI (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`coex_pti::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`coex_pti::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@coex_pti`] module"]
pub type COEX_PTI = crate::Reg<coex_pti::COEX_PTI_SPEC>;
#[doc = ""]
pub mod coex_pti;
#[doc = "CORE_DUMMY_DATA (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`core_dummy_data::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_dummy_data::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_dummy_data`] module"]
pub type CORE_DUMMY_DATA = crate::Reg<core_dummy_data::CORE_DUMMY_DATA_SPEC>;
#[doc = ""]
pub mod core_dummy_data;
#[doc = "TX_ABORT_INTERRUPT_CONTROL (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`tx_abort_interrupt_control::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_abort_interrupt_control::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tx_abort_interrupt_control`] module"]
pub type TX_ABORT_INTERRUPT_CONTROL =
    crate::Reg<tx_abort_interrupt_control::TX_ABORT_INTERRUPT_CONTROL_SPEC>;
#[doc = ""]
pub mod tx_abort_interrupt_control;
#[doc = "ENHANCE_ACK_CFG (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`enhance_ack_cfg::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`enhance_ack_cfg::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@enhance_ack_cfg`] module"]
pub type ENHANCE_ACK_CFG = crate::Reg<enhance_ack_cfg::ENHANCE_ACK_CFG_SPEC>;
#[doc = ""]
pub mod enhance_ack_cfg;
#[doc = "RX_STATUS (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`rx_status::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rx_status::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rx_status`] module"]
pub type RX_STATUS = crate::Reg<rx_status::RX_STATUS_SPEC>;
#[doc = ""]
pub mod rx_status;
#[doc = "TX_STATUS (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`tx_status::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_status::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tx_status`] module"]
pub type TX_STATUS = crate::Reg<tx_status::TX_STATUS_SPEC>;
#[doc = ""]
pub mod tx_status;
#[doc = "TXRX_STATUS (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`txrx_status::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`txrx_status::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@txrx_status`] module"]
pub type TXRX_STATUS = crate::Reg<txrx_status::TXRX_STATUS_SPEC>;
#[doc = ""]
pub mod txrx_status;
#[doc = "TX_CCM_SCHEDULE_STATUS (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`tx_ccm_schedule_status::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_ccm_schedule_status::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tx_ccm_schedule_status`] module"]
pub type TX_CCM_SCHEDULE_STATUS = crate::Reg<tx_ccm_schedule_status::TX_CCM_SCHEDULE_STATUS_SPEC>;
#[doc = ""]
pub mod tx_ccm_schedule_status;
#[doc = "CORE_GCK_CFG (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`core_gck_cfg::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`core_gck_cfg::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@core_gck_cfg`] module"]
pub type CORE_GCK_CFG = crate::Reg<core_gck_cfg::CORE_GCK_CFG_SPEC>;
#[doc = ""]
pub mod core_gck_cfg;
#[doc = "TEST_CONTROL (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`test_control::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`test_control::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@test_control`] module"]
pub type TEST_CONTROL = crate::Reg<test_control::TEST_CONTROL_SPEC>;
#[doc = ""]
pub mod test_control;
#[doc = "DTM_CONFIG (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`dtm_config::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dtm_config::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dtm_config`] module"]
pub type DTM_CONFIG = crate::Reg<dtm_config::DTM_CONFIG_SPEC>;
#[doc = ""]
pub mod dtm_config;
#[doc = "DTM_TX_PKT_CONFIG (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`dtm_tx_pkt_config::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dtm_tx_pkt_config::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dtm_tx_pkt_config`] module"]
pub type DTM_TX_PKT_CONFIG = crate::Reg<dtm_tx_pkt_config::DTM_TX_PKT_CONFIG_SPEC>;
#[doc = ""]
pub mod dtm_tx_pkt_config;
#[doc = "DTM_PKT_COUNTER (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`dtm_pkt_counter::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dtm_pkt_counter::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dtm_pkt_counter`] module"]
pub type DTM_PKT_COUNTER = crate::Reg<dtm_pkt_counter::DTM_PKT_COUNTER_SPEC>;
#[doc = ""]
pub mod dtm_pkt_counter;
#[doc = "RX_LENGTH (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`rx_length::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rx_length::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rx_length`] module"]
pub type RX_LENGTH = crate::Reg<rx_length::RX_LENGTH_SPEC>;
#[doc = ""]
pub mod rx_length;
#[doc = "Cluster TIME%s, containing TIME?_THRESHOLD, TIME?_VALUE"]
pub use self::time::TIME;
#[doc = r"Cluster"]
#[doc = "Cluster TIME%s, containing TIME?_THRESHOLD, TIME?_VALUE"]
pub mod time;
#[doc = "CLK_COUNTER_MATCH_VAL (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`clk_counter_match_val::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clk_counter_match_val::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@clk_counter_match_val`] module"]
pub type CLK_COUNTER_MATCH_VAL = crate::Reg<clk_counter_match_val::CLK_COUNTER_MATCH_VAL_SPEC>;
#[doc = ""]
pub mod clk_counter_match_val;
#[doc = "CLK_COUNTER (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`clk_counter::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clk_counter::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@clk_counter`] module"]
pub type CLK_COUNTER = crate::Reg<clk_counter::CLK_COUNTER_SPEC>;
#[doc = ""]
pub mod clk_counter;
#[doc = "IFS_COUNTER (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`ifs_counter::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ifs_counter::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ifs_counter`] module"]
pub type IFS_COUNTER = crate::Reg<ifs_counter::IFS_COUNTER_SPEC>;
#[doc = ""]
pub mod ifs_counter;
#[doc = "SFD_WAIT_SYMBOL (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`sfd_wait_symbol::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sfd_wait_symbol::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sfd_wait_symbol`] module"]
pub type SFD_WAIT_SYMBOL = crate::Reg<sfd_wait_symbol::SFD_WAIT_SYMBOL_SPEC>;
#[doc = ""]
pub mod sfd_wait_symbol;
#[doc = "TXRX_PATH_DELAY (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`txrx_path_delay::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`txrx_path_delay::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@txrx_path_delay`] module"]
pub type TXRX_PATH_DELAY = crate::Reg<txrx_path_delay::TXRX_PATH_DELAY_SPEC>;
#[doc = ""]
pub mod txrx_path_delay;
#[doc = "BB_CLK (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`bb_clk::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`bb_clk::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@bb_clk`] module"]
pub type BB_CLK = crate::Reg<bb_clk::BB_CLK_SPEC>;
#[doc = ""]
pub mod bb_clk;
#[doc = "TXDMA_ADDR (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`txdma_addr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`txdma_addr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@txdma_addr`] module"]
pub type TXDMA_ADDR = crate::Reg<txdma_addr::TXDMA_ADDR_SPEC>;
#[doc = ""]
pub mod txdma_addr;
#[doc = "TXDMA_CTRL_STATE (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`txdma_ctrl_state::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`txdma_ctrl_state::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@txdma_ctrl_state`] module"]
pub type TXDMA_CTRL_STATE = crate::Reg<txdma_ctrl_state::TXDMA_CTRL_STATE_SPEC>;
#[doc = ""]
pub mod txdma_ctrl_state;
#[doc = "TXDMA_ERR (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`txdma_err::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`txdma_err::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@txdma_err`] module"]
pub type TXDMA_ERR = crate::Reg<txdma_err::TXDMA_ERR_SPEC>;
#[doc = ""]
pub mod txdma_err;
#[doc = "RXDMA_ADDR (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`rxdma_addr::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rxdma_addr::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rxdma_addr`] module"]
pub type RXDMA_ADDR = crate::Reg<rxdma_addr::RXDMA_ADDR_SPEC>;
#[doc = ""]
pub mod rxdma_addr;
#[doc = "RXDMA_CTRL_STATE (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`rxdma_ctrl_state::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rxdma_ctrl_state::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rxdma_ctrl_state`] module"]
pub type RXDMA_CTRL_STATE = crate::Reg<rxdma_ctrl_state::RXDMA_CTRL_STATE_SPEC>;
#[doc = ""]
pub mod rxdma_ctrl_state;
#[doc = "RXDMA_ERR (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`rxdma_err::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rxdma_err::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rxdma_err`] module"]
pub type RXDMA_ERR = crate::Reg<rxdma_err::RXDMA_ERR_SPEC>;
#[doc = ""]
pub mod rxdma_err;
#[doc = "DMA_GCK_CFG (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`dma_gck_cfg::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dma_gck_cfg::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dma_gck_cfg`] module"]
pub type DMA_GCK_CFG = crate::Reg<dma_gck_cfg::DMA_GCK_CFG_SPEC>;
#[doc = ""]
pub mod dma_gck_cfg;
#[doc = "DMA_DUMMY (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`dma_dummy::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dma_dummy::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dma_dummy`] module"]
pub type DMA_DUMMY = crate::Reg<dma_dummy::DMA_DUMMY_SPEC>;
#[doc = ""]
pub mod dma_dummy;
#[doc = "PAON_DELAY (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`paon_delay::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`paon_delay::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@paon_delay`] module"]
pub type PAON_DELAY = crate::Reg<paon_delay::PAON_DELAY_SPEC>;
#[doc = ""]
pub mod paon_delay;
#[doc = "TXON_DELAY (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`txon_delay::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`txon_delay::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@txon_delay`] module"]
pub type TXON_DELAY = crate::Reg<txon_delay::TXON_DELAY_SPEC>;
#[doc = ""]
pub mod txon_delay;
#[doc = "TXEN_STOP_DELAY (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`txen_stop_delay::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`txen_stop_delay::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@txen_stop_delay`] module"]
pub type TXEN_STOP_DELAY = crate::Reg<txen_stop_delay::TXEN_STOP_DELAY_SPEC>;
#[doc = ""]
pub mod txen_stop_delay;
#[doc = "TXOFF_DELAY (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`txoff_delay::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`txoff_delay::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@txoff_delay`] module"]
pub type TXOFF_DELAY = crate::Reg<txoff_delay::TXOFF_DELAY_SPEC>;
#[doc = ""]
pub mod txoff_delay;
#[doc = "RXON_DELAY (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`rxon_delay::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rxon_delay::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rxon_delay`] module"]
pub type RXON_DELAY = crate::Reg<rxon_delay::RXON_DELAY_SPEC>;
#[doc = ""]
pub mod rxon_delay;
#[doc = "TXRX_SWITCH_DELAY (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`txrx_switch_delay::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`txrx_switch_delay::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@txrx_switch_delay`] module"]
pub type TXRX_SWITCH_DELAY = crate::Reg<txrx_switch_delay::TXRX_SWITCH_DELAY_SPEC>;
#[doc = ""]
pub mod txrx_switch_delay;
#[doc = "CONT_RX_DELAY (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`cont_rx_delay::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cont_rx_delay::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cont_rx_delay`] module"]
pub type CONT_RX_DELAY = crate::Reg<cont_rx_delay::CONT_RX_DELAY_SPEC>;
#[doc = ""]
pub mod cont_rx_delay;
#[doc = "DCDC_CTRL (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`dcdc_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dcdc_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@dcdc_ctrl`] module"]
pub type DCDC_CTRL = crate::Reg<dcdc_ctrl::DCDC_CTRL_SPEC>;
#[doc = ""]
pub mod dcdc_ctrl;
#[doc = "DEBUG_CTRL (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`debug_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`debug_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@debug_ctrl`] module"]
pub type DEBUG_CTRL = crate::Reg<debug_ctrl::DEBUG_CTRL_SPEC>;
#[doc = ""]
pub mod debug_ctrl;
#[doc = "SEC_CTRL (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`sec_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sec_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sec_ctrl`] module"]
pub type SEC_CTRL = crate::Reg<sec_ctrl::SEC_CTRL_SPEC>;
#[doc = ""]
pub mod sec_ctrl;
#[doc = "SEC_EXTEND_ADDRESS0 (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`sec_extend_address0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sec_extend_address0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sec_extend_address0`] module"]
pub type SEC_EXTEND_ADDRESS0 = crate::Reg<sec_extend_address0::SEC_EXTEND_ADDRESS0_SPEC>;
#[doc = ""]
pub mod sec_extend_address0;
#[doc = "SEC_EXTEND_ADDRESS1 (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`sec_extend_address1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sec_extend_address1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sec_extend_address1`] module"]
pub type SEC_EXTEND_ADDRESS1 = crate::Reg<sec_extend_address1::SEC_EXTEND_ADDRESS1_SPEC>;
#[doc = ""]
pub mod sec_extend_address1;
#[doc = "SEC_KEY (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`sec_key::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sec_key::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sec_key`] module"]
pub type SEC_KEY = crate::Reg<sec_key::SEC_KEY_SPEC>;
#[doc = ""]
pub mod sec_key;
#[doc = "SFD_TIMEOUT_CNT (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`sfd_timeout_cnt::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sfd_timeout_cnt::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@sfd_timeout_cnt`] module"]
pub type SFD_TIMEOUT_CNT = crate::Reg<sfd_timeout_cnt::SFD_TIMEOUT_CNT_SPEC>;
#[doc = ""]
pub mod sfd_timeout_cnt;
#[doc = "CRC_ERROR_CNT (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`crc_error_cnt::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`crc_error_cnt::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@crc_error_cnt`] module"]
pub type CRC_ERROR_CNT = crate::Reg<crc_error_cnt::CRC_ERROR_CNT_SPEC>;
#[doc = ""]
pub mod crc_error_cnt;
#[doc = "ED_ABORT_CNT (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`ed_abort_cnt::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ed_abort_cnt::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ed_abort_cnt`] module"]
pub type ED_ABORT_CNT = crate::Reg<ed_abort_cnt::ED_ABORT_CNT_SPEC>;
#[doc = ""]
pub mod ed_abort_cnt;
#[doc = "CCA_FAIL_CNT (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`cca_fail_cnt::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cca_fail_cnt::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cca_fail_cnt`] module"]
pub type CCA_FAIL_CNT = crate::Reg<cca_fail_cnt::CCA_FAIL_CNT_SPEC>;
#[doc = ""]
pub mod cca_fail_cnt;
#[doc = "RX_FILTER_FAIL_CNT (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`rx_filter_fail_cnt::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rx_filter_fail_cnt::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rx_filter_fail_cnt`] module"]
pub type RX_FILTER_FAIL_CNT = crate::Reg<rx_filter_fail_cnt::RX_FILTER_FAIL_CNT_SPEC>;
#[doc = ""]
pub mod rx_filter_fail_cnt;
#[doc = "NO_RSS_DETECT_CNT (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`no_rss_detect_cnt::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`no_rss_detect_cnt::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@no_rss_detect_cnt`] module"]
pub type NO_RSS_DETECT_CNT = crate::Reg<no_rss_detect_cnt::NO_RSS_DETECT_CNT_SPEC>;
#[doc = ""]
pub mod no_rss_detect_cnt;
#[doc = "RX_ABORT_COEX_CNT (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`rx_abort_coex_cnt::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rx_abort_coex_cnt::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rx_abort_coex_cnt`] module"]
pub type RX_ABORT_COEX_CNT = crate::Reg<rx_abort_coex_cnt::RX_ABORT_COEX_CNT_SPEC>;
#[doc = ""]
pub mod rx_abort_coex_cnt;
#[doc = "RX_RESTART_CNT (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`rx_restart_cnt::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rx_restart_cnt::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rx_restart_cnt`] module"]
pub type RX_RESTART_CNT = crate::Reg<rx_restart_cnt::RX_RESTART_CNT_SPEC>;
#[doc = ""]
pub mod rx_restart_cnt;
#[doc = "TX_ACK_ABORT_COEX_CNT (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`tx_ack_abort_coex_cnt::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_ack_abort_coex_cnt::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tx_ack_abort_coex_cnt`] module"]
pub type TX_ACK_ABORT_COEX_CNT = crate::Reg<tx_ack_abort_coex_cnt::TX_ACK_ABORT_COEX_CNT_SPEC>;
#[doc = ""]
pub mod tx_ack_abort_coex_cnt;
#[doc = "ED_SCAN_COEX_CNT (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`ed_scan_coex_cnt::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ed_scan_coex_cnt::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ed_scan_coex_cnt`] module"]
pub type ED_SCAN_COEX_CNT = crate::Reg<ed_scan_coex_cnt::ED_SCAN_COEX_CNT_SPEC>;
#[doc = ""]
pub mod ed_scan_coex_cnt;
#[doc = "RX_ACK_ABORT_COEX_CNT (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`rx_ack_abort_coex_cnt::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rx_ack_abort_coex_cnt::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rx_ack_abort_coex_cnt`] module"]
pub type RX_ACK_ABORT_COEX_CNT = crate::Reg<rx_ack_abort_coex_cnt::RX_ACK_ABORT_COEX_CNT_SPEC>;
#[doc = ""]
pub mod rx_ack_abort_coex_cnt;
#[doc = "RX_ACK_TIMEOUT_CNT (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`rx_ack_timeout_cnt::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rx_ack_timeout_cnt::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rx_ack_timeout_cnt`] module"]
pub type RX_ACK_TIMEOUT_CNT = crate::Reg<rx_ack_timeout_cnt::RX_ACK_TIMEOUT_CNT_SPEC>;
#[doc = ""]
pub mod rx_ack_timeout_cnt;
#[doc = "TX_BREAK_COEX_CNT (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`tx_break_coex_cnt::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_break_coex_cnt::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tx_break_coex_cnt`] module"]
pub type TX_BREAK_COEX_CNT = crate::Reg<tx_break_coex_cnt::TX_BREAK_COEX_CNT_SPEC>;
#[doc = ""]
pub mod tx_break_coex_cnt;
#[doc = "TX_SECURITY_ERROR_CNT (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`tx_security_error_cnt::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_security_error_cnt::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tx_security_error_cnt`] module"]
pub type TX_SECURITY_ERROR_CNT = crate::Reg<tx_security_error_cnt::TX_SECURITY_ERROR_CNT_SPEC>;
#[doc = ""]
pub mod tx_security_error_cnt;
#[doc = "CCA_BUSY_CNT (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`cca_busy_cnt::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cca_busy_cnt::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@cca_busy_cnt`] module"]
pub type CCA_BUSY_CNT = crate::Reg<cca_busy_cnt::CCA_BUSY_CNT_SPEC>;
#[doc = ""]
pub mod cca_busy_cnt;
#[doc = "ERROR_CNT_CLEAR (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`error_cnt_clear::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`error_cnt_clear::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@error_cnt_clear`] module"]
pub type ERROR_CNT_CLEAR = crate::Reg<error_cnt_clear::ERROR_CNT_CLEAR_SPEC>;
#[doc = ""]
pub mod error_cnt_clear;
pub use crate::aes::{date as mac_date, DATE as MAC_DATE};
