#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    ep1: EP1,
    ep1_conf: EP1_CONF,
    int_raw: INT_RAW,
    int_st: INT_ST,
    int_ena: INT_ENA,
    int_clr: INT_CLR,
    conf0: CONF0,
    test: TEST,
    jfifo_st: JFIFO_ST,
    fram_num: FRAM_NUM,
    in_ep0_st: IN_EP0_ST,
    in_ep1_st: IN_EP1_ST,
    in_ep2_st: IN_EP2_ST,
    in_ep3_st: IN_EP3_ST,
    out_ep0_st: OUT_EP0_ST,
    out_ep1_st: OUT_EP1_ST,
    out_ep2_st: OUT_EP2_ST,
    misc_conf: MISC_CONF,
    mem_conf: MEM_CONF,
    chip_rst: CHIP_RST,
    set_line_code_w0: SET_LINE_CODE_W0,
    set_line_code_w1: SET_LINE_CODE_W1,
    get_line_code_w0: GET_LINE_CODE_W0,
    get_line_code_w1: GET_LINE_CODE_W1,
    config_update: CONFIG_UPDATE,
    ser_afifo_config: SER_AFIFO_CONFIG,
    bus_reset_st: BUS_RESET_ST,
    _reserved27: [u8; 0x14],
    date: DATE,
}
impl RegisterBlock {
    #[doc = "0x00 - FIFO access for the CDC-ACM data IN and OUT endpoints."]
    #[inline(always)]
    pub const fn ep1(&self) -> &EP1 {
        &self.ep1
    }
    #[doc = "0x04 - Configuration and control registers for the CDC-ACM FIFOs."]
    #[inline(always)]
    pub const fn ep1_conf(&self) -> &EP1_CONF {
        &self.ep1_conf
    }
    #[doc = "0x08 - Interrupt raw status register."]
    #[inline(always)]
    pub const fn int_raw(&self) -> &INT_RAW {
        &self.int_raw
    }
    #[doc = "0x0c - Interrupt status register."]
    #[inline(always)]
    pub const fn int_st(&self) -> &INT_ST {
        &self.int_st
    }
    #[doc = "0x10 - Interrupt enable status register."]
    #[inline(always)]
    pub const fn int_ena(&self) -> &INT_ENA {
        &self.int_ena
    }
    #[doc = "0x14 - Interrupt clear status register."]
    #[inline(always)]
    pub const fn int_clr(&self) -> &INT_CLR {
        &self.int_clr
    }
    #[doc = "0x18 - PHY hardware configuration."]
    #[inline(always)]
    pub const fn conf0(&self) -> &CONF0 {
        &self.conf0
    }
    #[doc = "0x1c - Registers used for debugging the PHY."]
    #[inline(always)]
    pub const fn test(&self) -> &TEST {
        &self.test
    }
    #[doc = "0x20 - JTAG FIFO status and control registers."]
    #[inline(always)]
    pub const fn jfifo_st(&self) -> &JFIFO_ST {
        &self.jfifo_st
    }
    #[doc = "0x24 - Last received SOF frame index register."]
    #[inline(always)]
    pub const fn fram_num(&self) -> &FRAM_NUM {
        &self.fram_num
    }
    #[doc = "0x28 - Control IN endpoint status information."]
    #[inline(always)]
    pub const fn in_ep0_st(&self) -> &IN_EP0_ST {
        &self.in_ep0_st
    }
    #[doc = "0x2c - CDC-ACM IN endpoint status information."]
    #[inline(always)]
    pub const fn in_ep1_st(&self) -> &IN_EP1_ST {
        &self.in_ep1_st
    }
    #[doc = "0x30 - CDC-ACM interrupt IN endpoint status information."]
    #[inline(always)]
    pub const fn in_ep2_st(&self) -> &IN_EP2_ST {
        &self.in_ep2_st
    }
    #[doc = "0x34 - JTAG IN endpoint status information."]
    #[inline(always)]
    pub const fn in_ep3_st(&self) -> &IN_EP3_ST {
        &self.in_ep3_st
    }
    #[doc = "0x38 - Control OUT endpoint status information."]
    #[inline(always)]
    pub const fn out_ep0_st(&self) -> &OUT_EP0_ST {
        &self.out_ep0_st
    }
    #[doc = "0x3c - CDC-ACM OUT endpoint status information."]
    #[inline(always)]
    pub const fn out_ep1_st(&self) -> &OUT_EP1_ST {
        &self.out_ep1_st
    }
    #[doc = "0x40 - JTAG OUT endpoint status information."]
    #[inline(always)]
    pub const fn out_ep2_st(&self) -> &OUT_EP2_ST {
        &self.out_ep2_st
    }
    #[doc = "0x44 - Clock enable control"]
    #[inline(always)]
    pub const fn misc_conf(&self) -> &MISC_CONF {
        &self.misc_conf
    }
    #[doc = "0x48 - Memory power control"]
    #[inline(always)]
    pub const fn mem_conf(&self) -> &MEM_CONF {
        &self.mem_conf
    }
    #[doc = "0x4c - CDC-ACM chip reset control."]
    #[inline(always)]
    pub const fn chip_rst(&self) -> &CHIP_RST {
        &self.chip_rst
    }
    #[doc = "0x50 - W0 of SET_LINE_CODING command."]
    #[inline(always)]
    pub const fn set_line_code_w0(&self) -> &SET_LINE_CODE_W0 {
        &self.set_line_code_w0
    }
    #[doc = "0x54 - W1 of SET_LINE_CODING command."]
    #[inline(always)]
    pub const fn set_line_code_w1(&self) -> &SET_LINE_CODE_W1 {
        &self.set_line_code_w1
    }
    #[doc = "0x58 - W0 of GET_LINE_CODING command."]
    #[inline(always)]
    pub const fn get_line_code_w0(&self) -> &GET_LINE_CODE_W0 {
        &self.get_line_code_w0
    }
    #[doc = "0x5c - W1 of GET_LINE_CODING command."]
    #[inline(always)]
    pub const fn get_line_code_w1(&self) -> &GET_LINE_CODE_W1 {
        &self.get_line_code_w1
    }
    #[doc = "0x60 - Configuration registers' value update"]
    #[inline(always)]
    pub const fn config_update(&self) -> &CONFIG_UPDATE {
        &self.config_update
    }
    #[doc = "0x64 - Serial AFIFO configure register"]
    #[inline(always)]
    pub const fn ser_afifo_config(&self) -> &SER_AFIFO_CONFIG {
        &self.ser_afifo_config
    }
    #[doc = "0x68 - USB Bus reset status register"]
    #[inline(always)]
    pub const fn bus_reset_st(&self) -> &BUS_RESET_ST {
        &self.bus_reset_st
    }
    #[doc = "0x80 - Date register"]
    #[inline(always)]
    pub const fn date(&self) -> &DATE {
        &self.date
    }
}
#[doc = "EP1 (rw) register accessor: FIFO access for the CDC-ACM data IN and OUT endpoints.\n\nYou can [`read`](crate::Reg::read) this register and get [`ep1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ep1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ep1`] module"]
pub type EP1 = crate::Reg<ep1::EP1_SPEC>;
#[doc = "FIFO access for the CDC-ACM data IN and OUT endpoints."]
pub mod ep1;
#[doc = "EP1_CONF (rw) register accessor: Configuration and control registers for the CDC-ACM FIFOs.\n\nYou can [`read`](crate::Reg::read) this register and get [`ep1_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ep1_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ep1_conf`] module"]
pub type EP1_CONF = crate::Reg<ep1_conf::EP1_CONF_SPEC>;
#[doc = "Configuration and control registers for the CDC-ACM FIFOs."]
pub mod ep1_conf;
#[doc = "INT_RAW (rw) register accessor: Interrupt raw status register.\n\nYou can [`read`](crate::Reg::read) this register and get [`int_raw::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_raw::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_raw`] module"]
pub type INT_RAW = crate::Reg<int_raw::INT_RAW_SPEC>;
#[doc = "Interrupt raw status register."]
pub mod int_raw;
#[doc = "INT_ST (r) register accessor: Interrupt status register.\n\nYou can [`read`](crate::Reg::read) this register and get [`int_st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_st`] module"]
pub type INT_ST = crate::Reg<int_st::INT_ST_SPEC>;
#[doc = "Interrupt status register."]
pub mod int_st;
#[doc = "INT_ENA (rw) register accessor: Interrupt enable status register.\n\nYou can [`read`](crate::Reg::read) this register and get [`int_ena::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_ena::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_ena`] module"]
pub type INT_ENA = crate::Reg<int_ena::INT_ENA_SPEC>;
#[doc = "Interrupt enable status register."]
pub mod int_ena;
#[doc = "INT_CLR (w) register accessor: Interrupt clear status register.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_clr::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@int_clr`] module"]
pub type INT_CLR = crate::Reg<int_clr::INT_CLR_SPEC>;
#[doc = "Interrupt clear status register."]
pub mod int_clr;
#[doc = "CONF0 (rw) register accessor: PHY hardware configuration.\n\nYou can [`read`](crate::Reg::read) this register and get [`conf0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@conf0`] module"]
pub type CONF0 = crate::Reg<conf0::CONF0_SPEC>;
#[doc = "PHY hardware configuration."]
pub mod conf0;
#[doc = "TEST (rw) register accessor: Registers used for debugging the PHY.\n\nYou can [`read`](crate::Reg::read) this register and get [`test::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`test::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@test`] module"]
pub type TEST = crate::Reg<test::TEST_SPEC>;
#[doc = "Registers used for debugging the PHY."]
pub mod test;
#[doc = "JFIFO_ST (rw) register accessor: JTAG FIFO status and control registers.\n\nYou can [`read`](crate::Reg::read) this register and get [`jfifo_st::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`jfifo_st::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@jfifo_st`] module"]
pub type JFIFO_ST = crate::Reg<jfifo_st::JFIFO_ST_SPEC>;
#[doc = "JTAG FIFO status and control registers."]
pub mod jfifo_st;
#[doc = "FRAM_NUM (r) register accessor: Last received SOF frame index register.\n\nYou can [`read`](crate::Reg::read) this register and get [`fram_num::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@fram_num`] module"]
pub type FRAM_NUM = crate::Reg<fram_num::FRAM_NUM_SPEC>;
#[doc = "Last received SOF frame index register."]
pub mod fram_num;
#[doc = "IN_EP0_ST (r) register accessor: Control IN endpoint status information.\n\nYou can [`read`](crate::Reg::read) this register and get [`in_ep0_st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@in_ep0_st`] module"]
pub type IN_EP0_ST = crate::Reg<in_ep0_st::IN_EP0_ST_SPEC>;
#[doc = "Control IN endpoint status information."]
pub mod in_ep0_st;
#[doc = "IN_EP1_ST (r) register accessor: CDC-ACM IN endpoint status information.\n\nYou can [`read`](crate::Reg::read) this register and get [`in_ep1_st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@in_ep1_st`] module"]
pub type IN_EP1_ST = crate::Reg<in_ep1_st::IN_EP1_ST_SPEC>;
#[doc = "CDC-ACM IN endpoint status information."]
pub mod in_ep1_st;
#[doc = "IN_EP2_ST (r) register accessor: CDC-ACM interrupt IN endpoint status information.\n\nYou can [`read`](crate::Reg::read) this register and get [`in_ep2_st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@in_ep2_st`] module"]
pub type IN_EP2_ST = crate::Reg<in_ep2_st::IN_EP2_ST_SPEC>;
#[doc = "CDC-ACM interrupt IN endpoint status information."]
pub mod in_ep2_st;
#[doc = "IN_EP3_ST (r) register accessor: JTAG IN endpoint status information.\n\nYou can [`read`](crate::Reg::read) this register and get [`in_ep3_st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@in_ep3_st`] module"]
pub type IN_EP3_ST = crate::Reg<in_ep3_st::IN_EP3_ST_SPEC>;
#[doc = "JTAG IN endpoint status information."]
pub mod in_ep3_st;
#[doc = "OUT_EP0_ST (r) register accessor: Control OUT endpoint status information.\n\nYou can [`read`](crate::Reg::read) this register and get [`out_ep0_st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@out_ep0_st`] module"]
pub type OUT_EP0_ST = crate::Reg<out_ep0_st::OUT_EP0_ST_SPEC>;
#[doc = "Control OUT endpoint status information."]
pub mod out_ep0_st;
#[doc = "OUT_EP1_ST (r) register accessor: CDC-ACM OUT endpoint status information.\n\nYou can [`read`](crate::Reg::read) this register and get [`out_ep1_st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@out_ep1_st`] module"]
pub type OUT_EP1_ST = crate::Reg<out_ep1_st::OUT_EP1_ST_SPEC>;
#[doc = "CDC-ACM OUT endpoint status information."]
pub mod out_ep1_st;
#[doc = "OUT_EP2_ST (r) register accessor: JTAG OUT endpoint status information.\n\nYou can [`read`](crate::Reg::read) this register and get [`out_ep2_st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@out_ep2_st`] module"]
pub type OUT_EP2_ST = crate::Reg<out_ep2_st::OUT_EP2_ST_SPEC>;
#[doc = "JTAG OUT endpoint status information."]
pub mod out_ep2_st;
#[doc = "MISC_CONF (rw) register accessor: Clock enable control\n\nYou can [`read`](crate::Reg::read) this register and get [`misc_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`misc_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@misc_conf`] module"]
pub type MISC_CONF = crate::Reg<misc_conf::MISC_CONF_SPEC>;
#[doc = "Clock enable control"]
pub mod misc_conf;
#[doc = "MEM_CONF (rw) register accessor: Memory power control\n\nYou can [`read`](crate::Reg::read) this register and get [`mem_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`mem_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@mem_conf`] module"]
pub type MEM_CONF = crate::Reg<mem_conf::MEM_CONF_SPEC>;
#[doc = "Memory power control"]
pub mod mem_conf;
#[doc = "CHIP_RST (rw) register accessor: CDC-ACM chip reset control.\n\nYou can [`read`](crate::Reg::read) this register and get [`chip_rst::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`chip_rst::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@chip_rst`] module"]
pub type CHIP_RST = crate::Reg<chip_rst::CHIP_RST_SPEC>;
#[doc = "CDC-ACM chip reset control."]
pub mod chip_rst;
#[doc = "SET_LINE_CODE_W0 (r) register accessor: W0 of SET_LINE_CODING command.\n\nYou can [`read`](crate::Reg::read) this register and get [`set_line_code_w0::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@set_line_code_w0`] module"]
pub type SET_LINE_CODE_W0 = crate::Reg<set_line_code_w0::SET_LINE_CODE_W0_SPEC>;
#[doc = "W0 of SET_LINE_CODING command."]
pub mod set_line_code_w0;
#[doc = "SET_LINE_CODE_W1 (r) register accessor: W1 of SET_LINE_CODING command.\n\nYou can [`read`](crate::Reg::read) this register and get [`set_line_code_w1::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@set_line_code_w1`] module"]
pub type SET_LINE_CODE_W1 = crate::Reg<set_line_code_w1::SET_LINE_CODE_W1_SPEC>;
#[doc = "W1 of SET_LINE_CODING command."]
pub mod set_line_code_w1;
#[doc = "GET_LINE_CODE_W0 (rw) register accessor: W0 of GET_LINE_CODING command.\n\nYou can [`read`](crate::Reg::read) this register and get [`get_line_code_w0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`get_line_code_w0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@get_line_code_w0`] module"]
pub type GET_LINE_CODE_W0 = crate::Reg<get_line_code_w0::GET_LINE_CODE_W0_SPEC>;
#[doc = "W0 of GET_LINE_CODING command."]
pub mod get_line_code_w0;
#[doc = "GET_LINE_CODE_W1 (rw) register accessor: W1 of GET_LINE_CODING command.\n\nYou can [`read`](crate::Reg::read) this register and get [`get_line_code_w1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`get_line_code_w1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@get_line_code_w1`] module"]
pub type GET_LINE_CODE_W1 = crate::Reg<get_line_code_w1::GET_LINE_CODE_W1_SPEC>;
#[doc = "W1 of GET_LINE_CODING command."]
pub mod get_line_code_w1;
#[doc = "CONFIG_UPDATE (w) register accessor: Configuration registers' value update\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`config_update::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@config_update`] module"]
pub type CONFIG_UPDATE = crate::Reg<config_update::CONFIG_UPDATE_SPEC>;
#[doc = "Configuration registers' value update"]
pub mod config_update;
#[doc = "SER_AFIFO_CONFIG (rw) register accessor: Serial AFIFO configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`ser_afifo_config::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ser_afifo_config::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ser_afifo_config`] module"]
pub type SER_AFIFO_CONFIG = crate::Reg<ser_afifo_config::SER_AFIFO_CONFIG_SPEC>;
#[doc = "Serial AFIFO configure register"]
pub mod ser_afifo_config;
#[doc = "BUS_RESET_ST (r) register accessor: USB Bus reset status register\n\nYou can [`read`](crate::Reg::read) this register and get [`bus_reset_st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@bus_reset_st`] module"]
pub type BUS_RESET_ST = crate::Reg<bus_reset_st::BUS_RESET_ST_SPEC>;
#[doc = "USB Bus reset status register"]
pub mod bus_reset_st;
pub use crate::aes::{date, DATE};
