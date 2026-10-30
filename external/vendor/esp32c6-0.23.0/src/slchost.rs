#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    _reserved0: [u8; 0x10],
    func2_0: FUNC2_0,
    func2_1: FUNC2_1,
    _reserved2: [u8; 0x08],
    func2_2: FUNC2_2,
    _reserved3: [u8; 0x10],
    gpio_status0: GPIO_STATUS0,
    gpio_status1: GPIO_STATUS1,
    gpio_in0: GPIO_IN0,
    gpio_in1: GPIO_IN1,
    slc0host_token_rdata: SLC0HOST_TOKEN_RDATA,
    slc0_host_pf: SLC0_HOST_PF,
    slc1_host_pf: SLC1_HOST_PF,
    slc0host_int_raw: SLC0HOST_INT_RAW,
    slc1host_int_raw: SLC1HOST_INT_RAW,
    slc0host_int_st: SLC0HOST_INT_ST,
    slc1host_int_st: SLC1HOST_INT_ST,
    pkt_len: PKT_LEN,
    state_w0: STATE_W0,
    state_w1: STATE_W1,
    conf_w0: CONF_W0,
    conf_w1: CONF_W1,
    conf_w2: CONF_W2,
    conf_w3: CONF_W3,
    conf_w4: CONF_W4,
    conf_w5: CONF_W5,
    win_cmd: WIN_CMD,
    conf_w6: CONF_W6,
    conf_w7: CONF_W7,
    pkt_len0: PKT_LEN0,
    pkt_len1: PKT_LEN1,
    pkt_len2: PKT_LEN2,
    conf_w8: CONF_W8,
    conf_w9: CONF_W9,
    conf_w10: CONF_W10,
    conf_w11: CONF_W11,
    conf_w12: CONF_W12,
    conf_w13: CONF_W13,
    conf_w14: CONF_W14,
    conf_w15: CONF_W15,
    check_sum0: CHECK_SUM0,
    check_sum1: CHECK_SUM1,
    slc1host_token_rdata: SLC1HOST_TOKEN_RDATA,
    slc0host_token_wdata: SLC0HOST_TOKEN_WDATA,
    slc1host_token_wdata: SLC1HOST_TOKEN_WDATA,
    token_con: TOKEN_CON,
    slc0host_int_clr: SLC0HOST_INT_CLR,
    slc1host_int_clr: SLC1HOST_INT_CLR,
    slc0host_func1_int_ena: SLC0HOST_FUNC1_INT_ENA,
    slc1host_func1_int_ena: SLC1HOST_FUNC1_INT_ENA,
    slc0host_func2_int_ena: SLC0HOST_FUNC2_INT_ENA,
    slc1host_func2_int_ena: SLC1HOST_FUNC2_INT_ENA,
    slc0host_int_ena: SLC0HOST_INT_ENA,
    slc1host_int_ena: SLC1HOST_INT_ENA,
    slc0host_rx_infor: SLC0HOST_RX_INFOR,
    slc1host_rx_infor: SLC1HOST_RX_INFOR,
    slc0host_len_wd: SLC0HOST_LEN_WD,
    slc_apbwin_wdata: SLC_APBWIN_WDATA,
    slc_apbwin_conf: SLC_APBWIN_CONF,
    slc_apbwin_rdata: SLC_APBWIN_RDATA,
    rdclr0: RDCLR0,
    rdclr1: RDCLR1,
    slc0host_int_ena1: SLC0HOST_INT_ENA1,
    slc1host_int_ena1: SLC1HOST_INT_ENA1,
    _reserved61: [u8; 0x5c],
    slchostdate: SLCHOSTDATE,
    slchostid: SLCHOSTID,
    _reserved63: [u8; 0x70],
    conf: CONF,
    inf_st: INF_ST,
}
impl RegisterBlock {
    #[doc = "0x10 - *******Description***********"]
    #[inline(always)]
    pub const fn func2_0(&self) -> &FUNC2_0 {
        &self.func2_0
    }
    #[doc = "0x14 - *******Description***********"]
    #[inline(always)]
    pub const fn func2_1(&self) -> &FUNC2_1 {
        &self.func2_1
    }
    #[doc = "0x20 - *******Description***********"]
    #[inline(always)]
    pub const fn func2_2(&self) -> &FUNC2_2 {
        &self.func2_2
    }
    #[doc = "0x34 - *******Description***********"]
    #[inline(always)]
    pub const fn gpio_status0(&self) -> &GPIO_STATUS0 {
        &self.gpio_status0
    }
    #[doc = "0x38 - *******Description***********"]
    #[inline(always)]
    pub const fn gpio_status1(&self) -> &GPIO_STATUS1 {
        &self.gpio_status1
    }
    #[doc = "0x3c - *******Description***********"]
    #[inline(always)]
    pub const fn gpio_in0(&self) -> &GPIO_IN0 {
        &self.gpio_in0
    }
    #[doc = "0x40 - *******Description***********"]
    #[inline(always)]
    pub const fn gpio_in1(&self) -> &GPIO_IN1 {
        &self.gpio_in1
    }
    #[doc = "0x44 - *******Description***********"]
    #[inline(always)]
    pub const fn slc0host_token_rdata(&self) -> &SLC0HOST_TOKEN_RDATA {
        &self.slc0host_token_rdata
    }
    #[doc = "0x48 - *******Description***********"]
    #[inline(always)]
    pub const fn slc0_host_pf(&self) -> &SLC0_HOST_PF {
        &self.slc0_host_pf
    }
    #[doc = "0x4c - *******Description***********"]
    #[inline(always)]
    pub const fn slc1_host_pf(&self) -> &SLC1_HOST_PF {
        &self.slc1_host_pf
    }
    #[doc = "0x50 - *******Description***********"]
    #[inline(always)]
    pub const fn slc0host_int_raw(&self) -> &SLC0HOST_INT_RAW {
        &self.slc0host_int_raw
    }
    #[doc = "0x54 - *******Description***********"]
    #[inline(always)]
    pub const fn slc1host_int_raw(&self) -> &SLC1HOST_INT_RAW {
        &self.slc1host_int_raw
    }
    #[doc = "0x58 - *******Description***********"]
    #[inline(always)]
    pub const fn slc0host_int_st(&self) -> &SLC0HOST_INT_ST {
        &self.slc0host_int_st
    }
    #[doc = "0x5c - *******Description***********"]
    #[inline(always)]
    pub const fn slc1host_int_st(&self) -> &SLC1HOST_INT_ST {
        &self.slc1host_int_st
    }
    #[doc = "0x60 - *******Description***********"]
    #[inline(always)]
    pub const fn pkt_len(&self) -> &PKT_LEN {
        &self.pkt_len
    }
    #[doc = "0x64 - *******Description***********"]
    #[inline(always)]
    pub const fn state_w0(&self) -> &STATE_W0 {
        &self.state_w0
    }
    #[doc = "0x68 - *******Description***********"]
    #[inline(always)]
    pub const fn state_w1(&self) -> &STATE_W1 {
        &self.state_w1
    }
    #[doc = "0x6c - *******Description***********"]
    #[inline(always)]
    pub const fn conf_w0(&self) -> &CONF_W0 {
        &self.conf_w0
    }
    #[doc = "0x70 - *******Description***********"]
    #[inline(always)]
    pub const fn conf_w1(&self) -> &CONF_W1 {
        &self.conf_w1
    }
    #[doc = "0x74 - *******Description***********"]
    #[inline(always)]
    pub const fn conf_w2(&self) -> &CONF_W2 {
        &self.conf_w2
    }
    #[doc = "0x78 - *******Description***********"]
    #[inline(always)]
    pub const fn conf_w3(&self) -> &CONF_W3 {
        &self.conf_w3
    }
    #[doc = "0x7c - *******Description***********"]
    #[inline(always)]
    pub const fn conf_w4(&self) -> &CONF_W4 {
        &self.conf_w4
    }
    #[doc = "0x80 - *******Description***********"]
    #[inline(always)]
    pub const fn conf_w5(&self) -> &CONF_W5 {
        &self.conf_w5
    }
    #[doc = "0x84 - *******Description***********"]
    #[inline(always)]
    pub const fn win_cmd(&self) -> &WIN_CMD {
        &self.win_cmd
    }
    #[doc = "0x88 - *******Description***********"]
    #[inline(always)]
    pub const fn conf_w6(&self) -> &CONF_W6 {
        &self.conf_w6
    }
    #[doc = "0x8c - *******Description***********"]
    #[inline(always)]
    pub const fn conf_w7(&self) -> &CONF_W7 {
        &self.conf_w7
    }
    #[doc = "0x90 - *******Description***********"]
    #[inline(always)]
    pub const fn pkt_len0(&self) -> &PKT_LEN0 {
        &self.pkt_len0
    }
    #[doc = "0x94 - *******Description***********"]
    #[inline(always)]
    pub const fn pkt_len1(&self) -> &PKT_LEN1 {
        &self.pkt_len1
    }
    #[doc = "0x98 - *******Description***********"]
    #[inline(always)]
    pub const fn pkt_len2(&self) -> &PKT_LEN2 {
        &self.pkt_len2
    }
    #[doc = "0x9c - *******Description***********"]
    #[inline(always)]
    pub const fn conf_w8(&self) -> &CONF_W8 {
        &self.conf_w8
    }
    #[doc = "0xa0 - *******Description***********"]
    #[inline(always)]
    pub const fn conf_w9(&self) -> &CONF_W9 {
        &self.conf_w9
    }
    #[doc = "0xa4 - *******Description***********"]
    #[inline(always)]
    pub const fn conf_w10(&self) -> &CONF_W10 {
        &self.conf_w10
    }
    #[doc = "0xa8 - *******Description***********"]
    #[inline(always)]
    pub const fn conf_w11(&self) -> &CONF_W11 {
        &self.conf_w11
    }
    #[doc = "0xac - *******Description***********"]
    #[inline(always)]
    pub const fn conf_w12(&self) -> &CONF_W12 {
        &self.conf_w12
    }
    #[doc = "0xb0 - *******Description***********"]
    #[inline(always)]
    pub const fn conf_w13(&self) -> &CONF_W13 {
        &self.conf_w13
    }
    #[doc = "0xb4 - *******Description***********"]
    #[inline(always)]
    pub const fn conf_w14(&self) -> &CONF_W14 {
        &self.conf_w14
    }
    #[doc = "0xb8 - *******Description***********"]
    #[inline(always)]
    pub const fn conf_w15(&self) -> &CONF_W15 {
        &self.conf_w15
    }
    #[doc = "0xbc - *******Description***********"]
    #[inline(always)]
    pub const fn check_sum0(&self) -> &CHECK_SUM0 {
        &self.check_sum0
    }
    #[doc = "0xc0 - *******Description***********"]
    #[inline(always)]
    pub const fn check_sum1(&self) -> &CHECK_SUM1 {
        &self.check_sum1
    }
    #[doc = "0xc4 - *******Description***********"]
    #[inline(always)]
    pub const fn slc1host_token_rdata(&self) -> &SLC1HOST_TOKEN_RDATA {
        &self.slc1host_token_rdata
    }
    #[doc = "0xc8 - *******Description***********"]
    #[inline(always)]
    pub const fn slc0host_token_wdata(&self) -> &SLC0HOST_TOKEN_WDATA {
        &self.slc0host_token_wdata
    }
    #[doc = "0xcc - *******Description***********"]
    #[inline(always)]
    pub const fn slc1host_token_wdata(&self) -> &SLC1HOST_TOKEN_WDATA {
        &self.slc1host_token_wdata
    }
    #[doc = "0xd0 - *******Description***********"]
    #[inline(always)]
    pub const fn token_con(&self) -> &TOKEN_CON {
        &self.token_con
    }
    #[doc = "0xd4 - *******Description***********"]
    #[inline(always)]
    pub const fn slc0host_int_clr(&self) -> &SLC0HOST_INT_CLR {
        &self.slc0host_int_clr
    }
    #[doc = "0xd8 - *******Description***********"]
    #[inline(always)]
    pub const fn slc1host_int_clr(&self) -> &SLC1HOST_INT_CLR {
        &self.slc1host_int_clr
    }
    #[doc = "0xdc - *******Description***********"]
    #[inline(always)]
    pub const fn slc0host_func1_int_ena(&self) -> &SLC0HOST_FUNC1_INT_ENA {
        &self.slc0host_func1_int_ena
    }
    #[doc = "0xe0 - *******Description***********"]
    #[inline(always)]
    pub const fn slc1host_func1_int_ena(&self) -> &SLC1HOST_FUNC1_INT_ENA {
        &self.slc1host_func1_int_ena
    }
    #[doc = "0xe4 - *******Description***********"]
    #[inline(always)]
    pub const fn slc0host_func2_int_ena(&self) -> &SLC0HOST_FUNC2_INT_ENA {
        &self.slc0host_func2_int_ena
    }
    #[doc = "0xe8 - *******Description***********"]
    #[inline(always)]
    pub const fn slc1host_func2_int_ena(&self) -> &SLC1HOST_FUNC2_INT_ENA {
        &self.slc1host_func2_int_ena
    }
    #[doc = "0xec - *******Description***********"]
    #[inline(always)]
    pub const fn slc0host_int_ena(&self) -> &SLC0HOST_INT_ENA {
        &self.slc0host_int_ena
    }
    #[doc = "0xf0 - *******Description***********"]
    #[inline(always)]
    pub const fn slc1host_int_ena(&self) -> &SLC1HOST_INT_ENA {
        &self.slc1host_int_ena
    }
    #[doc = "0xf4 - *******Description***********"]
    #[inline(always)]
    pub const fn slc0host_rx_infor(&self) -> &SLC0HOST_RX_INFOR {
        &self.slc0host_rx_infor
    }
    #[doc = "0xf8 - *******Description***********"]
    #[inline(always)]
    pub const fn slc1host_rx_infor(&self) -> &SLC1HOST_RX_INFOR {
        &self.slc1host_rx_infor
    }
    #[doc = "0xfc - *******Description***********"]
    #[inline(always)]
    pub const fn slc0host_len_wd(&self) -> &SLC0HOST_LEN_WD {
        &self.slc0host_len_wd
    }
    #[doc = "0x100 - *******Description***********"]
    #[inline(always)]
    pub const fn slc_apbwin_wdata(&self) -> &SLC_APBWIN_WDATA {
        &self.slc_apbwin_wdata
    }
    #[doc = "0x104 - *******Description***********"]
    #[inline(always)]
    pub const fn slc_apbwin_conf(&self) -> &SLC_APBWIN_CONF {
        &self.slc_apbwin_conf
    }
    #[doc = "0x108 - *******Description***********"]
    #[inline(always)]
    pub const fn slc_apbwin_rdata(&self) -> &SLC_APBWIN_RDATA {
        &self.slc_apbwin_rdata
    }
    #[doc = "0x10c - *******Description***********"]
    #[inline(always)]
    pub const fn rdclr0(&self) -> &RDCLR0 {
        &self.rdclr0
    }
    #[doc = "0x110 - *******Description***********"]
    #[inline(always)]
    pub const fn rdclr1(&self) -> &RDCLR1 {
        &self.rdclr1
    }
    #[doc = "0x114 - *******Description***********"]
    #[inline(always)]
    pub const fn slc0host_int_ena1(&self) -> &SLC0HOST_INT_ENA1 {
        &self.slc0host_int_ena1
    }
    #[doc = "0x118 - *******Description***********"]
    #[inline(always)]
    pub const fn slc1host_int_ena1(&self) -> &SLC1HOST_INT_ENA1 {
        &self.slc1host_int_ena1
    }
    #[doc = "0x178 - *******Description***********"]
    #[inline(always)]
    pub const fn slchostdate(&self) -> &SLCHOSTDATE {
        &self.slchostdate
    }
    #[doc = "0x17c - *******Description***********"]
    #[inline(always)]
    pub const fn slchostid(&self) -> &SLCHOSTID {
        &self.slchostid
    }
    #[doc = "0x1f0 - *******Description***********"]
    #[inline(always)]
    pub const fn conf(&self) -> &CONF {
        &self.conf
    }
    #[doc = "0x1f4 - *******Description***********"]
    #[inline(always)]
    pub const fn inf_st(&self) -> &INF_ST {
        &self.inf_st
    }
}
#[doc = "FUNC2_0 (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`func2_0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`func2_0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@func2_0`] module"]
pub type FUNC2_0 = crate::Reg<func2_0::FUNC2_0_SPEC>;
#[doc = "*******Description***********"]
pub mod func2_0;
#[doc = "FUNC2_1 (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`func2_1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`func2_1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@func2_1`] module"]
pub type FUNC2_1 = crate::Reg<func2_1::FUNC2_1_SPEC>;
#[doc = "*******Description***********"]
pub mod func2_1;
#[doc = "FUNC2_2 (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`func2_2::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`func2_2::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@func2_2`] module"]
pub type FUNC2_2 = crate::Reg<func2_2::FUNC2_2_SPEC>;
#[doc = "*******Description***********"]
pub mod func2_2;
#[doc = "GPIO_STATUS0 (r) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`gpio_status0::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@gpio_status0`] module"]
pub type GPIO_STATUS0 = crate::Reg<gpio_status0::GPIO_STATUS0_SPEC>;
#[doc = "*******Description***********"]
pub mod gpio_status0;
#[doc = "GPIO_STATUS1 (r) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`gpio_status1::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@gpio_status1`] module"]
pub type GPIO_STATUS1 = crate::Reg<gpio_status1::GPIO_STATUS1_SPEC>;
#[doc = "*******Description***********"]
pub mod gpio_status1;
#[doc = "GPIO_IN0 (r) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`gpio_in0::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@gpio_in0`] module"]
pub type GPIO_IN0 = crate::Reg<gpio_in0::GPIO_IN0_SPEC>;
#[doc = "*******Description***********"]
pub mod gpio_in0;
#[doc = "GPIO_IN1 (r) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`gpio_in1::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@gpio_in1`] module"]
pub type GPIO_IN1 = crate::Reg<gpio_in1::GPIO_IN1_SPEC>;
#[doc = "*******Description***********"]
pub mod gpio_in1;
#[doc = "SLC0HOST_TOKEN_RDATA (r) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0host_token_rdata::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0host_token_rdata`] module"]
pub type SLC0HOST_TOKEN_RDATA = crate::Reg<slc0host_token_rdata::SLC0HOST_TOKEN_RDATA_SPEC>;
#[doc = "*******Description***********"]
pub mod slc0host_token_rdata;
#[doc = "SLC0_HOST_PF (r) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0_host_pf::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0_host_pf`] module"]
pub type SLC0_HOST_PF = crate::Reg<slc0_host_pf::SLC0_HOST_PF_SPEC>;
#[doc = "*******Description***********"]
pub mod slc0_host_pf;
#[doc = "SLC1_HOST_PF (r) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1_host_pf::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc1_host_pf`] module"]
pub type SLC1_HOST_PF = crate::Reg<slc1_host_pf::SLC1_HOST_PF_SPEC>;
#[doc = "*******Description***********"]
pub mod slc1_host_pf;
#[doc = "SLC0HOST_INT_RAW (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0host_int_raw::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0host_int_raw::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0host_int_raw`] module"]
pub type SLC0HOST_INT_RAW = crate::Reg<slc0host_int_raw::SLC0HOST_INT_RAW_SPEC>;
#[doc = "*******Description***********"]
pub mod slc0host_int_raw;
#[doc = "SLC1HOST_INT_RAW (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1host_int_raw::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc1host_int_raw::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc1host_int_raw`] module"]
pub type SLC1HOST_INT_RAW = crate::Reg<slc1host_int_raw::SLC1HOST_INT_RAW_SPEC>;
#[doc = "*******Description***********"]
pub mod slc1host_int_raw;
#[doc = "SLC0HOST_INT_ST (r) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0host_int_st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0host_int_st`] module"]
pub type SLC0HOST_INT_ST = crate::Reg<slc0host_int_st::SLC0HOST_INT_ST_SPEC>;
#[doc = "*******Description***********"]
pub mod slc0host_int_st;
#[doc = "SLC1HOST_INT_ST (r) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1host_int_st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc1host_int_st`] module"]
pub type SLC1HOST_INT_ST = crate::Reg<slc1host_int_st::SLC1HOST_INT_ST_SPEC>;
#[doc = "*******Description***********"]
pub mod slc1host_int_st;
#[doc = "PKT_LEN (r) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`pkt_len::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pkt_len`] module"]
pub type PKT_LEN = crate::Reg<pkt_len::PKT_LEN_SPEC>;
#[doc = "*******Description***********"]
pub mod pkt_len;
#[doc = "STATE_W0 (r) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`state_w0::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@state_w0`] module"]
pub type STATE_W0 = crate::Reg<state_w0::STATE_W0_SPEC>;
#[doc = "*******Description***********"]
pub mod state_w0;
#[doc = "STATE_W1 (r) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`state_w1::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@state_w1`] module"]
pub type STATE_W1 = crate::Reg<state_w1::STATE_W1_SPEC>;
#[doc = "*******Description***********"]
pub mod state_w1;
#[doc = "CONF_W0 (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf_w0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf_w0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@conf_w0`] module"]
pub type CONF_W0 = crate::Reg<conf_w0::CONF_W0_SPEC>;
#[doc = "*******Description***********"]
pub mod conf_w0;
#[doc = "CONF_W1 (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf_w1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf_w1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@conf_w1`] module"]
pub type CONF_W1 = crate::Reg<conf_w1::CONF_W1_SPEC>;
#[doc = "*******Description***********"]
pub mod conf_w1;
#[doc = "CONF_W2 (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf_w2::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf_w2::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@conf_w2`] module"]
pub type CONF_W2 = crate::Reg<conf_w2::CONF_W2_SPEC>;
#[doc = "*******Description***********"]
pub mod conf_w2;
#[doc = "CONF_W3 (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf_w3::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf_w3::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@conf_w3`] module"]
pub type CONF_W3 = crate::Reg<conf_w3::CONF_W3_SPEC>;
#[doc = "*******Description***********"]
pub mod conf_w3;
#[doc = "CONF_W4 (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf_w4::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf_w4::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@conf_w4`] module"]
pub type CONF_W4 = crate::Reg<conf_w4::CONF_W4_SPEC>;
#[doc = "*******Description***********"]
pub mod conf_w4;
#[doc = "CONF_W5 (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf_w5::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf_w5::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@conf_w5`] module"]
pub type CONF_W5 = crate::Reg<conf_w5::CONF_W5_SPEC>;
#[doc = "*******Description***********"]
pub mod conf_w5;
#[doc = "WIN_CMD (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`win_cmd::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`win_cmd::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@win_cmd`] module"]
pub type WIN_CMD = crate::Reg<win_cmd::WIN_CMD_SPEC>;
#[doc = "*******Description***********"]
pub mod win_cmd;
#[doc = "CONF_W6 (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf_w6::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf_w6::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@conf_w6`] module"]
pub type CONF_W6 = crate::Reg<conf_w6::CONF_W6_SPEC>;
#[doc = "*******Description***********"]
pub mod conf_w6;
#[doc = "CONF_W7 (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf_w7::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf_w7::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@conf_w7`] module"]
pub type CONF_W7 = crate::Reg<conf_w7::CONF_W7_SPEC>;
#[doc = "*******Description***********"]
pub mod conf_w7;
#[doc = "PKT_LEN0 (r) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`pkt_len0::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pkt_len0`] module"]
pub type PKT_LEN0 = crate::Reg<pkt_len0::PKT_LEN0_SPEC>;
#[doc = "*******Description***********"]
pub mod pkt_len0;
#[doc = "PKT_LEN1 (r) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`pkt_len1::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pkt_len1`] module"]
pub type PKT_LEN1 = crate::Reg<pkt_len1::PKT_LEN1_SPEC>;
#[doc = "*******Description***********"]
pub mod pkt_len1;
#[doc = "PKT_LEN2 (r) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`pkt_len2::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pkt_len2`] module"]
pub type PKT_LEN2 = crate::Reg<pkt_len2::PKT_LEN2_SPEC>;
#[doc = "*******Description***********"]
pub mod pkt_len2;
#[doc = "CONF_W8 (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf_w8::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf_w8::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@conf_w8`] module"]
pub type CONF_W8 = crate::Reg<conf_w8::CONF_W8_SPEC>;
#[doc = "*******Description***********"]
pub mod conf_w8;
#[doc = "CONF_W9 (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf_w9::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf_w9::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@conf_w9`] module"]
pub type CONF_W9 = crate::Reg<conf_w9::CONF_W9_SPEC>;
#[doc = "*******Description***********"]
pub mod conf_w9;
#[doc = "CONF_W10 (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf_w10::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf_w10::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@conf_w10`] module"]
pub type CONF_W10 = crate::Reg<conf_w10::CONF_W10_SPEC>;
#[doc = "*******Description***********"]
pub mod conf_w10;
#[doc = "CONF_W11 (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf_w11::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf_w11::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@conf_w11`] module"]
pub type CONF_W11 = crate::Reg<conf_w11::CONF_W11_SPEC>;
#[doc = "*******Description***********"]
pub mod conf_w11;
#[doc = "CONF_W12 (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf_w12::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf_w12::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@conf_w12`] module"]
pub type CONF_W12 = crate::Reg<conf_w12::CONF_W12_SPEC>;
#[doc = "*******Description***********"]
pub mod conf_w12;
#[doc = "CONF_W13 (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf_w13::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf_w13::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@conf_w13`] module"]
pub type CONF_W13 = crate::Reg<conf_w13::CONF_W13_SPEC>;
#[doc = "*******Description***********"]
pub mod conf_w13;
#[doc = "CONF_W14 (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf_w14::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf_w14::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@conf_w14`] module"]
pub type CONF_W14 = crate::Reg<conf_w14::CONF_W14_SPEC>;
#[doc = "*******Description***********"]
pub mod conf_w14;
#[doc = "CONF_W15 (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf_w15::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf_w15::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@conf_w15`] module"]
pub type CONF_W15 = crate::Reg<conf_w15::CONF_W15_SPEC>;
#[doc = "*******Description***********"]
pub mod conf_w15;
#[doc = "CHECK_SUM0 (r) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`check_sum0::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@check_sum0`] module"]
pub type CHECK_SUM0 = crate::Reg<check_sum0::CHECK_SUM0_SPEC>;
#[doc = "*******Description***********"]
pub mod check_sum0;
#[doc = "CHECK_SUM1 (r) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`check_sum1::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@check_sum1`] module"]
pub type CHECK_SUM1 = crate::Reg<check_sum1::CHECK_SUM1_SPEC>;
#[doc = "*******Description***********"]
pub mod check_sum1;
#[doc = "SLC1HOST_TOKEN_RDATA (r) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1host_token_rdata::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc1host_token_rdata`] module"]
pub type SLC1HOST_TOKEN_RDATA = crate::Reg<slc1host_token_rdata::SLC1HOST_TOKEN_RDATA_SPEC>;
#[doc = "*******Description***********"]
pub mod slc1host_token_rdata;
#[doc = "SLC0HOST_TOKEN_WDATA (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0host_token_wdata::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0host_token_wdata::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0host_token_wdata`] module"]
pub type SLC0HOST_TOKEN_WDATA = crate::Reg<slc0host_token_wdata::SLC0HOST_TOKEN_WDATA_SPEC>;
#[doc = "*******Description***********"]
pub mod slc0host_token_wdata;
#[doc = "SLC1HOST_TOKEN_WDATA (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1host_token_wdata::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc1host_token_wdata::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc1host_token_wdata`] module"]
pub type SLC1HOST_TOKEN_WDATA = crate::Reg<slc1host_token_wdata::SLC1HOST_TOKEN_WDATA_SPEC>;
#[doc = "*******Description***********"]
pub mod slc1host_token_wdata;
#[doc = "TOKEN_CON (w) register accessor: *******Description***********\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`token_con::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@token_con`] module"]
pub type TOKEN_CON = crate::Reg<token_con::TOKEN_CON_SPEC>;
#[doc = "*******Description***********"]
pub mod token_con;
#[doc = "SLC0HOST_INT_CLR (w) register accessor: *******Description***********\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0host_int_clr::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0host_int_clr`] module"]
pub type SLC0HOST_INT_CLR = crate::Reg<slc0host_int_clr::SLC0HOST_INT_CLR_SPEC>;
#[doc = "*******Description***********"]
pub mod slc0host_int_clr;
#[doc = "SLC1HOST_INT_CLR (w) register accessor: *******Description***********\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc1host_int_clr::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc1host_int_clr`] module"]
pub type SLC1HOST_INT_CLR = crate::Reg<slc1host_int_clr::SLC1HOST_INT_CLR_SPEC>;
#[doc = "*******Description***********"]
pub mod slc1host_int_clr;
#[doc = "SLC0HOST_FUNC1_INT_ENA (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0host_func1_int_ena::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0host_func1_int_ena::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0host_func1_int_ena`] module"]
pub type SLC0HOST_FUNC1_INT_ENA = crate::Reg<slc0host_func1_int_ena::SLC0HOST_FUNC1_INT_ENA_SPEC>;
#[doc = "*******Description***********"]
pub mod slc0host_func1_int_ena;
#[doc = "SLC1HOST_FUNC1_INT_ENA (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1host_func1_int_ena::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc1host_func1_int_ena::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc1host_func1_int_ena`] module"]
pub type SLC1HOST_FUNC1_INT_ENA = crate::Reg<slc1host_func1_int_ena::SLC1HOST_FUNC1_INT_ENA_SPEC>;
#[doc = "*******Description***********"]
pub mod slc1host_func1_int_ena;
#[doc = "SLC0HOST_FUNC2_INT_ENA (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0host_func2_int_ena::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0host_func2_int_ena::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0host_func2_int_ena`] module"]
pub type SLC0HOST_FUNC2_INT_ENA = crate::Reg<slc0host_func2_int_ena::SLC0HOST_FUNC2_INT_ENA_SPEC>;
#[doc = "*******Description***********"]
pub mod slc0host_func2_int_ena;
#[doc = "SLC1HOST_FUNC2_INT_ENA (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1host_func2_int_ena::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc1host_func2_int_ena::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc1host_func2_int_ena`] module"]
pub type SLC1HOST_FUNC2_INT_ENA = crate::Reg<slc1host_func2_int_ena::SLC1HOST_FUNC2_INT_ENA_SPEC>;
#[doc = "*******Description***********"]
pub mod slc1host_func2_int_ena;
#[doc = "SLC0HOST_INT_ENA (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0host_int_ena::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0host_int_ena::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0host_int_ena`] module"]
pub type SLC0HOST_INT_ENA = crate::Reg<slc0host_int_ena::SLC0HOST_INT_ENA_SPEC>;
#[doc = "*******Description***********"]
pub mod slc0host_int_ena;
#[doc = "SLC1HOST_INT_ENA (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1host_int_ena::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc1host_int_ena::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc1host_int_ena`] module"]
pub type SLC1HOST_INT_ENA = crate::Reg<slc1host_int_ena::SLC1HOST_INT_ENA_SPEC>;
#[doc = "*******Description***********"]
pub mod slc1host_int_ena;
#[doc = "SLC0HOST_RX_INFOR (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0host_rx_infor::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0host_rx_infor::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0host_rx_infor`] module"]
pub type SLC0HOST_RX_INFOR = crate::Reg<slc0host_rx_infor::SLC0HOST_RX_INFOR_SPEC>;
#[doc = "*******Description***********"]
pub mod slc0host_rx_infor;
#[doc = "SLC1HOST_RX_INFOR (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1host_rx_infor::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc1host_rx_infor::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc1host_rx_infor`] module"]
pub type SLC1HOST_RX_INFOR = crate::Reg<slc1host_rx_infor::SLC1HOST_RX_INFOR_SPEC>;
#[doc = "*******Description***********"]
pub mod slc1host_rx_infor;
#[doc = "SLC0HOST_LEN_WD (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0host_len_wd::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0host_len_wd::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0host_len_wd`] module"]
pub type SLC0HOST_LEN_WD = crate::Reg<slc0host_len_wd::SLC0HOST_LEN_WD_SPEC>;
#[doc = "*******Description***********"]
pub mod slc0host_len_wd;
#[doc = "SLC_APBWIN_WDATA (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc_apbwin_wdata::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc_apbwin_wdata::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc_apbwin_wdata`] module"]
pub type SLC_APBWIN_WDATA = crate::Reg<slc_apbwin_wdata::SLC_APBWIN_WDATA_SPEC>;
#[doc = "*******Description***********"]
pub mod slc_apbwin_wdata;
#[doc = "SLC_APBWIN_CONF (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc_apbwin_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc_apbwin_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc_apbwin_conf`] module"]
pub type SLC_APBWIN_CONF = crate::Reg<slc_apbwin_conf::SLC_APBWIN_CONF_SPEC>;
#[doc = "*******Description***********"]
pub mod slc_apbwin_conf;
#[doc = "SLC_APBWIN_RDATA (r) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc_apbwin_rdata::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc_apbwin_rdata`] module"]
pub type SLC_APBWIN_RDATA = crate::Reg<slc_apbwin_rdata::SLC_APBWIN_RDATA_SPEC>;
#[doc = "*******Description***********"]
pub mod slc_apbwin_rdata;
#[doc = "RDCLR0 (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`rdclr0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rdclr0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rdclr0`] module"]
pub type RDCLR0 = crate::Reg<rdclr0::RDCLR0_SPEC>;
#[doc = "*******Description***********"]
pub mod rdclr0;
#[doc = "RDCLR1 (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`rdclr1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`rdclr1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@rdclr1`] module"]
pub type RDCLR1 = crate::Reg<rdclr1::RDCLR1_SPEC>;
#[doc = "*******Description***********"]
pub mod rdclr1;
#[doc = "SLC0HOST_INT_ENA1 (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc0host_int_ena1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc0host_int_ena1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc0host_int_ena1`] module"]
pub type SLC0HOST_INT_ENA1 = crate::Reg<slc0host_int_ena1::SLC0HOST_INT_ENA1_SPEC>;
#[doc = "*******Description***********"]
pub mod slc0host_int_ena1;
#[doc = "SLC1HOST_INT_ENA1 (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slc1host_int_ena1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slc1host_int_ena1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slc1host_int_ena1`] module"]
pub type SLC1HOST_INT_ENA1 = crate::Reg<slc1host_int_ena1::SLC1HOST_INT_ENA1_SPEC>;
#[doc = "*******Description***********"]
pub mod slc1host_int_ena1;
#[doc = "SLCHOSTDATE (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slchostdate::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slchostdate::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slchostdate`] module"]
pub type SLCHOSTDATE = crate::Reg<slchostdate::SLCHOSTDATE_SPEC>;
#[doc = "*******Description***********"]
pub mod slchostdate;
#[doc = "SLCHOSTID (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slchostid::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slchostid::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@slchostid`] module"]
pub type SLCHOSTID = crate::Reg<slchostid::SLCHOSTID_SPEC>;
#[doc = "*******Description***********"]
pub mod slchostid;
#[doc = "CONF (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@conf`] module"]
pub type CONF = crate::Reg<conf::CONF_SPEC>;
#[doc = "*******Description***********"]
pub mod conf;
#[doc = "INF_ST (rw) register accessor: *******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`inf_st::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`inf_st::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@inf_st`] module"]
pub type INF_ST = crate::Reg<inf_st::INF_ST_SPEC>;
#[doc = "*******Description***********"]
pub mod inf_st;
