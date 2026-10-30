#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Cluster CH%s, containing IN_CONF0_CH?, IN_CONF1_CH?, INFIFO_STATUS_CH?, IN_POP_CH?, IN_LINK_CH?, IN_STATE_CH?, IN_SUC_EOF_DES_ADDR_CH?, IN_ERR_EOF_DES_ADDR_CH?, IN_DSCR_CH?, IN_DSCR_BF0_CH?, IN_DSCR_BF1_CH?, IN_PRI_CH?, IN_PERI_SEL_CH?, OUT_CONF0_CH?, OUT_CONF1_CH?, OUTFIFO_STATUS_CH?, OUT_PUSH_CH?, OUT_LINK_CH?, OUT_STATE_CH?, OUT_EOF_DES_ADDR_CH?, OUT_EOF_BFR_DES_ADDR_CH?, OUT_DSCR_CH?, OUT_DSCR_BF0_CH?, OUT_DSCR_BF1_CH?, OUT_PRI_CH?, OUT_PERI_SEL_CH?"]
pub struct CH {
    in_conf0: IN_CONF0,
    in_conf1: IN_CONF1,
    infifo_status: INFIFO_STATUS,
    in_pop: IN_POP,
    in_link: IN_LINK,
    in_state: IN_STATE,
    in_suc_eof_des_addr: IN_SUC_EOF_DES_ADDR,
    in_err_eof_des_addr: IN_ERR_EOF_DES_ADDR,
    in_dscr: IN_DSCR,
    in_dscr_bf0: IN_DSCR_BF0,
    in_dscr_bf1: IN_DSCR_BF1,
    in_pri: IN_PRI,
    in_peri_sel: IN_PERI_SEL,
    _reserved13: [u8; 0x2c],
    out_conf0: OUT_CONF0,
    out_conf1: OUT_CONF1,
    outfifo_status: OUTFIFO_STATUS,
    out_push: OUT_PUSH,
    out_link: OUT_LINK,
    out_state: OUT_STATE,
    out_eof_des_addr: OUT_EOF_DES_ADDR,
    out_eof_bfr_des_addr: OUT_EOF_BFR_DES_ADDR,
    out_dscr: OUT_DSCR,
    out_dscr_bf0: OUT_DSCR_BF0,
    out_dscr_bf1: OUT_DSCR_BF1,
    out_pri: OUT_PRI,
    out_peri_sel: OUT_PERI_SEL,
    _reserved_end: [u8; 0x2c],
}
impl CH {
    #[doc = "0x00 - DMA_IN_CONF0_CH0_REG."]
    #[inline(always)]
    pub const fn in_conf0(&self) -> &IN_CONF0 {
        &self.in_conf0
    }
    #[doc = "0x04 - DMA_IN_CONF1_CH0_REG."]
    #[inline(always)]
    pub const fn in_conf1(&self) -> &IN_CONF1 {
        &self.in_conf1
    }
    #[doc = "0x08 - DMA_INFIFO_STATUS_CH0_REG."]
    #[inline(always)]
    pub const fn infifo_status(&self) -> &INFIFO_STATUS {
        &self.infifo_status
    }
    #[doc = "0x0c - DMA_IN_POP_CH0_REG."]
    #[inline(always)]
    pub const fn in_pop(&self) -> &IN_POP {
        &self.in_pop
    }
    #[doc = "0x10 - DMA_IN_LINK_CH0_REG."]
    #[inline(always)]
    pub const fn in_link(&self) -> &IN_LINK {
        &self.in_link
    }
    #[doc = "0x14 - DMA_IN_STATE_CH0_REG."]
    #[inline(always)]
    pub const fn in_state(&self) -> &IN_STATE {
        &self.in_state
    }
    #[doc = "0x18 - DMA_IN_SUC_EOF_DES_ADDR_CH0_REG."]
    #[inline(always)]
    pub const fn in_suc_eof_des_addr(&self) -> &IN_SUC_EOF_DES_ADDR {
        &self.in_suc_eof_des_addr
    }
    #[doc = "0x1c - DMA_IN_ERR_EOF_DES_ADDR_CH0_REG."]
    #[inline(always)]
    pub const fn in_err_eof_des_addr(&self) -> &IN_ERR_EOF_DES_ADDR {
        &self.in_err_eof_des_addr
    }
    #[doc = "0x20 - DMA_IN_DSCR_CH0_REG."]
    #[inline(always)]
    pub const fn in_dscr(&self) -> &IN_DSCR {
        &self.in_dscr
    }
    #[doc = "0x24 - DMA_IN_DSCR_BF0_CH0_REG."]
    #[inline(always)]
    pub const fn in_dscr_bf0(&self) -> &IN_DSCR_BF0 {
        &self.in_dscr_bf0
    }
    #[doc = "0x28 - DMA_IN_DSCR_BF1_CH0_REG."]
    #[inline(always)]
    pub const fn in_dscr_bf1(&self) -> &IN_DSCR_BF1 {
        &self.in_dscr_bf1
    }
    #[doc = "0x2c - DMA_IN_PRI_CH0_REG."]
    #[inline(always)]
    pub const fn in_pri(&self) -> &IN_PRI {
        &self.in_pri
    }
    #[doc = "0x30 - DMA_IN_PERI_SEL_CH0_REG."]
    #[inline(always)]
    pub const fn in_peri_sel(&self) -> &IN_PERI_SEL {
        &self.in_peri_sel
    }
    #[doc = "0x60 - DMA_OUT_CONF0_CH0_REG."]
    #[inline(always)]
    pub const fn out_conf0(&self) -> &OUT_CONF0 {
        &self.out_conf0
    }
    #[doc = "0x64 - DMA_OUT_CONF1_CH0_REG."]
    #[inline(always)]
    pub const fn out_conf1(&self) -> &OUT_CONF1 {
        &self.out_conf1
    }
    #[doc = "0x68 - DMA_OUTFIFO_STATUS_CH0_REG."]
    #[inline(always)]
    pub const fn outfifo_status(&self) -> &OUTFIFO_STATUS {
        &self.outfifo_status
    }
    #[doc = "0x6c - DMA_OUT_PUSH_CH0_REG."]
    #[inline(always)]
    pub const fn out_push(&self) -> &OUT_PUSH {
        &self.out_push
    }
    #[doc = "0x70 - DMA_OUT_LINK_CH0_REG."]
    #[inline(always)]
    pub const fn out_link(&self) -> &OUT_LINK {
        &self.out_link
    }
    #[doc = "0x74 - DMA_OUT_STATE_CH0_REG."]
    #[inline(always)]
    pub const fn out_state(&self) -> &OUT_STATE {
        &self.out_state
    }
    #[doc = "0x78 - DMA_OUT_EOF_DES_ADDR_CH0_REG."]
    #[inline(always)]
    pub const fn out_eof_des_addr(&self) -> &OUT_EOF_DES_ADDR {
        &self.out_eof_des_addr
    }
    #[doc = "0x7c - DMA_OUT_EOF_BFR_DES_ADDR_CH0_REG."]
    #[inline(always)]
    pub const fn out_eof_bfr_des_addr(&self) -> &OUT_EOF_BFR_DES_ADDR {
        &self.out_eof_bfr_des_addr
    }
    #[doc = "0x80 - DMA_OUT_DSCR_CH0_REG."]
    #[inline(always)]
    pub const fn out_dscr(&self) -> &OUT_DSCR {
        &self.out_dscr
    }
    #[doc = "0x84 - DMA_OUT_DSCR_BF0_CH0_REG."]
    #[inline(always)]
    pub const fn out_dscr_bf0(&self) -> &OUT_DSCR_BF0 {
        &self.out_dscr_bf0
    }
    #[doc = "0x88 - DMA_OUT_DSCR_BF1_CH0_REG."]
    #[inline(always)]
    pub const fn out_dscr_bf1(&self) -> &OUT_DSCR_BF1 {
        &self.out_dscr_bf1
    }
    #[doc = "0x8c - DMA_OUT_PRI_CH0_REG."]
    #[inline(always)]
    pub const fn out_pri(&self) -> &OUT_PRI {
        &self.out_pri
    }
    #[doc = "0x90 - DMA_OUT_PERI_SEL_CH0_REG."]
    #[inline(always)]
    pub const fn out_peri_sel(&self) -> &OUT_PERI_SEL {
        &self.out_peri_sel
    }
}
#[doc = "IN_CONF0 (rw) register accessor: DMA_IN_CONF0_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`in_conf0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`in_conf0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@in_conf0`] module"]
pub type IN_CONF0 = crate::Reg<in_conf0::IN_CONF0_SPEC>;
#[doc = "DMA_IN_CONF0_CH0_REG."]
pub mod in_conf0;
#[doc = "IN_CONF1 (rw) register accessor: DMA_IN_CONF1_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`in_conf1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`in_conf1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@in_conf1`] module"]
pub type IN_CONF1 = crate::Reg<in_conf1::IN_CONF1_SPEC>;
#[doc = "DMA_IN_CONF1_CH0_REG."]
pub mod in_conf1;
#[doc = "INFIFO_STATUS (r) register accessor: DMA_INFIFO_STATUS_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`infifo_status::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@infifo_status`] module"]
pub type INFIFO_STATUS = crate::Reg<infifo_status::INFIFO_STATUS_SPEC>;
#[doc = "DMA_INFIFO_STATUS_CH0_REG."]
pub mod infifo_status;
#[doc = "IN_POP (rw) register accessor: DMA_IN_POP_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`in_pop::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`in_pop::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@in_pop`] module"]
pub type IN_POP = crate::Reg<in_pop::IN_POP_SPEC>;
#[doc = "DMA_IN_POP_CH0_REG."]
pub mod in_pop;
#[doc = "IN_LINK (rw) register accessor: DMA_IN_LINK_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`in_link::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`in_link::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@in_link`] module"]
pub type IN_LINK = crate::Reg<in_link::IN_LINK_SPEC>;
#[doc = "DMA_IN_LINK_CH0_REG."]
pub mod in_link;
#[doc = "IN_STATE (r) register accessor: DMA_IN_STATE_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`in_state::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@in_state`] module"]
pub type IN_STATE = crate::Reg<in_state::IN_STATE_SPEC>;
#[doc = "DMA_IN_STATE_CH0_REG."]
pub mod in_state;
#[doc = "IN_SUC_EOF_DES_ADDR (r) register accessor: DMA_IN_SUC_EOF_DES_ADDR_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`in_suc_eof_des_addr::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@in_suc_eof_des_addr`] module"]
pub type IN_SUC_EOF_DES_ADDR = crate::Reg<in_suc_eof_des_addr::IN_SUC_EOF_DES_ADDR_SPEC>;
#[doc = "DMA_IN_SUC_EOF_DES_ADDR_CH0_REG."]
pub mod in_suc_eof_des_addr;
#[doc = "IN_ERR_EOF_DES_ADDR (r) register accessor: DMA_IN_ERR_EOF_DES_ADDR_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`in_err_eof_des_addr::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@in_err_eof_des_addr`] module"]
pub type IN_ERR_EOF_DES_ADDR = crate::Reg<in_err_eof_des_addr::IN_ERR_EOF_DES_ADDR_SPEC>;
#[doc = "DMA_IN_ERR_EOF_DES_ADDR_CH0_REG."]
pub mod in_err_eof_des_addr;
#[doc = "IN_DSCR (r) register accessor: DMA_IN_DSCR_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`in_dscr::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@in_dscr`] module"]
pub type IN_DSCR = crate::Reg<in_dscr::IN_DSCR_SPEC>;
#[doc = "DMA_IN_DSCR_CH0_REG."]
pub mod in_dscr;
#[doc = "IN_DSCR_BF0 (r) register accessor: DMA_IN_DSCR_BF0_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`in_dscr_bf0::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@in_dscr_bf0`] module"]
pub type IN_DSCR_BF0 = crate::Reg<in_dscr_bf0::IN_DSCR_BF0_SPEC>;
#[doc = "DMA_IN_DSCR_BF0_CH0_REG."]
pub mod in_dscr_bf0;
#[doc = "IN_DSCR_BF1 (r) register accessor: DMA_IN_DSCR_BF1_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`in_dscr_bf1::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@in_dscr_bf1`] module"]
pub type IN_DSCR_BF1 = crate::Reg<in_dscr_bf1::IN_DSCR_BF1_SPEC>;
#[doc = "DMA_IN_DSCR_BF1_CH0_REG."]
pub mod in_dscr_bf1;
#[doc = "IN_PRI (rw) register accessor: DMA_IN_PRI_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`in_pri::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`in_pri::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@in_pri`] module"]
pub type IN_PRI = crate::Reg<in_pri::IN_PRI_SPEC>;
#[doc = "DMA_IN_PRI_CH0_REG."]
pub mod in_pri;
#[doc = "IN_PERI_SEL (rw) register accessor: DMA_IN_PERI_SEL_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`in_peri_sel::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`in_peri_sel::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@in_peri_sel`] module"]
pub type IN_PERI_SEL = crate::Reg<in_peri_sel::IN_PERI_SEL_SPEC>;
#[doc = "DMA_IN_PERI_SEL_CH0_REG."]
pub mod in_peri_sel;
#[doc = "OUT_CONF0 (rw) register accessor: DMA_OUT_CONF0_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`out_conf0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`out_conf0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@out_conf0`] module"]
pub type OUT_CONF0 = crate::Reg<out_conf0::OUT_CONF0_SPEC>;
#[doc = "DMA_OUT_CONF0_CH0_REG."]
pub mod out_conf0;
#[doc = "OUT_CONF1 (rw) register accessor: DMA_OUT_CONF1_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`out_conf1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`out_conf1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@out_conf1`] module"]
pub type OUT_CONF1 = crate::Reg<out_conf1::OUT_CONF1_SPEC>;
#[doc = "DMA_OUT_CONF1_CH0_REG."]
pub mod out_conf1;
#[doc = "OUTFIFO_STATUS (r) register accessor: DMA_OUTFIFO_STATUS_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`outfifo_status::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@outfifo_status`] module"]
pub type OUTFIFO_STATUS = crate::Reg<outfifo_status::OUTFIFO_STATUS_SPEC>;
#[doc = "DMA_OUTFIFO_STATUS_CH0_REG."]
pub mod outfifo_status;
#[doc = "OUT_PUSH (rw) register accessor: DMA_OUT_PUSH_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`out_push::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`out_push::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@out_push`] module"]
pub type OUT_PUSH = crate::Reg<out_push::OUT_PUSH_SPEC>;
#[doc = "DMA_OUT_PUSH_CH0_REG."]
pub mod out_push;
#[doc = "OUT_LINK (rw) register accessor: DMA_OUT_LINK_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`out_link::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`out_link::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@out_link`] module"]
pub type OUT_LINK = crate::Reg<out_link::OUT_LINK_SPEC>;
#[doc = "DMA_OUT_LINK_CH0_REG."]
pub mod out_link;
#[doc = "OUT_STATE (r) register accessor: DMA_OUT_STATE_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`out_state::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@out_state`] module"]
pub type OUT_STATE = crate::Reg<out_state::OUT_STATE_SPEC>;
#[doc = "DMA_OUT_STATE_CH0_REG."]
pub mod out_state;
#[doc = "OUT_EOF_DES_ADDR (r) register accessor: DMA_OUT_EOF_DES_ADDR_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`out_eof_des_addr::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@out_eof_des_addr`] module"]
pub type OUT_EOF_DES_ADDR = crate::Reg<out_eof_des_addr::OUT_EOF_DES_ADDR_SPEC>;
#[doc = "DMA_OUT_EOF_DES_ADDR_CH0_REG."]
pub mod out_eof_des_addr;
#[doc = "OUT_EOF_BFR_DES_ADDR (r) register accessor: DMA_OUT_EOF_BFR_DES_ADDR_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`out_eof_bfr_des_addr::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@out_eof_bfr_des_addr`] module"]
pub type OUT_EOF_BFR_DES_ADDR = crate::Reg<out_eof_bfr_des_addr::OUT_EOF_BFR_DES_ADDR_SPEC>;
#[doc = "DMA_OUT_EOF_BFR_DES_ADDR_CH0_REG."]
pub mod out_eof_bfr_des_addr;
#[doc = "OUT_DSCR (r) register accessor: DMA_OUT_DSCR_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`out_dscr::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@out_dscr`] module"]
pub type OUT_DSCR = crate::Reg<out_dscr::OUT_DSCR_SPEC>;
#[doc = "DMA_OUT_DSCR_CH0_REG."]
pub mod out_dscr;
#[doc = "OUT_DSCR_BF0 (r) register accessor: DMA_OUT_DSCR_BF0_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`out_dscr_bf0::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@out_dscr_bf0`] module"]
pub type OUT_DSCR_BF0 = crate::Reg<out_dscr_bf0::OUT_DSCR_BF0_SPEC>;
#[doc = "DMA_OUT_DSCR_BF0_CH0_REG."]
pub mod out_dscr_bf0;
#[doc = "OUT_DSCR_BF1 (r) register accessor: DMA_OUT_DSCR_BF1_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`out_dscr_bf1::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@out_dscr_bf1`] module"]
pub type OUT_DSCR_BF1 = crate::Reg<out_dscr_bf1::OUT_DSCR_BF1_SPEC>;
#[doc = "DMA_OUT_DSCR_BF1_CH0_REG."]
pub mod out_dscr_bf1;
#[doc = "OUT_PRI (rw) register accessor: DMA_OUT_PRI_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`out_pri::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`out_pri::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@out_pri`] module"]
pub type OUT_PRI = crate::Reg<out_pri::OUT_PRI_SPEC>;
#[doc = "DMA_OUT_PRI_CH0_REG."]
pub mod out_pri;
#[doc = "OUT_PERI_SEL (rw) register accessor: DMA_OUT_PERI_SEL_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`out_peri_sel::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`out_peri_sel::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@out_peri_sel`] module"]
pub type OUT_PERI_SEL = crate::Reg<out_peri_sel::OUT_PERI_SEL_SPEC>;
#[doc = "DMA_OUT_PERI_SEL_CH0_REG."]
pub mod out_peri_sel;
