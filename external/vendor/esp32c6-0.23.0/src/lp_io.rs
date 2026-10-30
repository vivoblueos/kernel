#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    out_data: OUT_DATA,
    out_data_w1ts: OUT_DATA_W1TS,
    out_data_w1tc: OUT_DATA_W1TC,
    out_enable: OUT_ENABLE,
    out_enable_w1ts: OUT_ENABLE_W1TS,
    out_enable_w1tc: OUT_ENABLE_W1TC,
    status: STATUS,
    status_w1ts: STATUS_W1TS,
    status_w1tc: STATUS_W1TC,
    in_: IN,
    pin: [PIN; 8],
    gpio: [GPIO; 8],
    status_interrupt: STATUS_INTERRUPT,
    debug_sel0: DEBUG_SEL0,
    debug_sel1: DEBUG_SEL1,
    lpi2c: LPI2C,
    _reserved16: [u8; 0x0384],
    date: DATE,
}
impl RegisterBlock {
    #[doc = "0x00 - need des"]
    #[inline(always)]
    pub const fn out_data(&self) -> &OUT_DATA {
        &self.out_data
    }
    #[doc = "0x04 - need des"]
    #[inline(always)]
    pub const fn out_data_w1ts(&self) -> &OUT_DATA_W1TS {
        &self.out_data_w1ts
    }
    #[doc = "0x08 - need des"]
    #[inline(always)]
    pub const fn out_data_w1tc(&self) -> &OUT_DATA_W1TC {
        &self.out_data_w1tc
    }
    #[doc = "0x0c - need des"]
    #[inline(always)]
    pub const fn out_enable(&self) -> &OUT_ENABLE {
        &self.out_enable
    }
    #[doc = "0x10 - need des"]
    #[inline(always)]
    pub const fn out_enable_w1ts(&self) -> &OUT_ENABLE_W1TS {
        &self.out_enable_w1ts
    }
    #[doc = "0x14 - need des"]
    #[inline(always)]
    pub const fn out_enable_w1tc(&self) -> &OUT_ENABLE_W1TC {
        &self.out_enable_w1tc
    }
    #[doc = "0x18 - need des"]
    #[inline(always)]
    pub const fn status(&self) -> &STATUS {
        &self.status
    }
    #[doc = "0x1c - need des"]
    #[inline(always)]
    pub const fn status_w1ts(&self) -> &STATUS_W1TS {
        &self.status_w1ts
    }
    #[doc = "0x20 - need des"]
    #[inline(always)]
    pub const fn status_w1tc(&self) -> &STATUS_W1TC {
        &self.status_w1tc
    }
    #[doc = "0x24 - need des"]
    #[inline(always)]
    pub const fn in_(&self) -> &IN {
        &self.in_
    }
    #[doc = "0x28..0x48 - need des"]
    #[inline(always)]
    pub const fn pin(&self, n: usize) -> &PIN {
        &self.pin[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x28..0x48 - need des"]
    #[inline(always)]
    pub fn pin_iter(&self) -> impl Iterator<Item = &PIN> {
        self.pin.iter()
    }
    #[doc = "0x48..0x68 - need des"]
    #[inline(always)]
    pub const fn gpio(&self, n: usize) -> &GPIO {
        &self.gpio[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x48..0x68 - need des"]
    #[inline(always)]
    pub fn gpio_iter(&self) -> impl Iterator<Item = &GPIO> {
        self.gpio.iter()
    }
    #[doc = "0x68 - need des"]
    #[inline(always)]
    pub const fn status_interrupt(&self) -> &STATUS_INTERRUPT {
        &self.status_interrupt
    }
    #[doc = "0x6c - need des"]
    #[inline(always)]
    pub const fn debug_sel0(&self) -> &DEBUG_SEL0 {
        &self.debug_sel0
    }
    #[doc = "0x70 - need des"]
    #[inline(always)]
    pub const fn debug_sel1(&self) -> &DEBUG_SEL1 {
        &self.debug_sel1
    }
    #[doc = "0x74 - need des"]
    #[inline(always)]
    pub const fn lpi2c(&self) -> &LPI2C {
        &self.lpi2c
    }
    #[doc = "0x3fc - need des"]
    #[inline(always)]
    pub const fn date(&self) -> &DATE {
        &self.date
    }
}
#[doc = "OUT_DATA (rw) register accessor: need des\n\nYou can [`read`](crate::Reg::read) this register and get [`out_data::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`out_data::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@out_data`] module"]
pub type OUT_DATA = crate::Reg<out_data::OUT_DATA_SPEC>;
#[doc = "need des"]
pub mod out_data;
#[doc = "OUT_DATA_W1TS (w) register accessor: need des\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`out_data_w1ts::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@out_data_w1ts`] module"]
pub type OUT_DATA_W1TS = crate::Reg<out_data_w1ts::OUT_DATA_W1TS_SPEC>;
#[doc = "need des"]
pub mod out_data_w1ts;
#[doc = "OUT_DATA_W1TC (w) register accessor: need des\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`out_data_w1tc::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@out_data_w1tc`] module"]
pub type OUT_DATA_W1TC = crate::Reg<out_data_w1tc::OUT_DATA_W1TC_SPEC>;
#[doc = "need des"]
pub mod out_data_w1tc;
#[doc = "OUT_ENABLE (rw) register accessor: need des\n\nYou can [`read`](crate::Reg::read) this register and get [`out_enable::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`out_enable::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@out_enable`] module"]
pub type OUT_ENABLE = crate::Reg<out_enable::OUT_ENABLE_SPEC>;
#[doc = "need des"]
pub mod out_enable;
#[doc = "OUT_ENABLE_W1TS (w) register accessor: need des\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`out_enable_w1ts::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@out_enable_w1ts`] module"]
pub type OUT_ENABLE_W1TS = crate::Reg<out_enable_w1ts::OUT_ENABLE_W1TS_SPEC>;
#[doc = "need des"]
pub mod out_enable_w1ts;
#[doc = "OUT_ENABLE_W1TC (w) register accessor: need des\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`out_enable_w1tc::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@out_enable_w1tc`] module"]
pub type OUT_ENABLE_W1TC = crate::Reg<out_enable_w1tc::OUT_ENABLE_W1TC_SPEC>;
#[doc = "need des"]
pub mod out_enable_w1tc;
#[doc = "STATUS (rw) register accessor: need des\n\nYou can [`read`](crate::Reg::read) this register and get [`status::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`status::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@status`] module"]
pub type STATUS = crate::Reg<status::STATUS_SPEC>;
#[doc = "need des"]
pub mod status;
#[doc = "STATUS_W1TS (w) register accessor: need des\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`status_w1ts::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@status_w1ts`] module"]
pub type STATUS_W1TS = crate::Reg<status_w1ts::STATUS_W1TS_SPEC>;
#[doc = "need des"]
pub mod status_w1ts;
#[doc = "STATUS_W1TC (w) register accessor: need des\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`status_w1tc::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@status_w1tc`] module"]
pub type STATUS_W1TC = crate::Reg<status_w1tc::STATUS_W1TC_SPEC>;
#[doc = "need des"]
pub mod status_w1tc;
#[doc = "IN (r) register accessor: need des\n\nYou can [`read`](crate::Reg::read) this register and get [`in_::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@in_`] module"]
pub type IN = crate::Reg<in_::IN_SPEC>;
#[doc = "need des"]
pub mod in_;
#[doc = "PIN (rw) register accessor: need des\n\nYou can [`read`](crate::Reg::read) this register and get [`pin::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pin::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pin`] module"]
pub type PIN = crate::Reg<pin::PIN_SPEC>;
#[doc = "need des"]
pub mod pin;
#[doc = "GPIO (rw) register accessor: need des\n\nYou can [`read`](crate::Reg::read) this register and get [`gpio::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`gpio::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@gpio`] module"]
pub type GPIO = crate::Reg<gpio::GPIO_SPEC>;
#[doc = "need des"]
pub mod gpio;
#[doc = "STATUS_INTERRUPT (r) register accessor: need des\n\nYou can [`read`](crate::Reg::read) this register and get [`status_interrupt::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@status_interrupt`] module"]
pub type STATUS_INTERRUPT = crate::Reg<status_interrupt::STATUS_INTERRUPT_SPEC>;
#[doc = "need des"]
pub mod status_interrupt;
#[doc = "DEBUG_SEL0 (rw) register accessor: need des\n\nYou can [`read`](crate::Reg::read) this register and get [`debug_sel0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`debug_sel0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@debug_sel0`] module"]
pub type DEBUG_SEL0 = crate::Reg<debug_sel0::DEBUG_SEL0_SPEC>;
#[doc = "need des"]
pub mod debug_sel0;
#[doc = "DEBUG_SEL1 (rw) register accessor: need des\n\nYou can [`read`](crate::Reg::read) this register and get [`debug_sel1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`debug_sel1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@debug_sel1`] module"]
pub type DEBUG_SEL1 = crate::Reg<debug_sel1::DEBUG_SEL1_SPEC>;
#[doc = "need des"]
pub mod debug_sel1;
#[doc = "LPI2C (rw) register accessor: need des\n\nYou can [`read`](crate::Reg::read) this register and get [`lpi2c::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`lpi2c::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@lpi2c`] module"]
pub type LPI2C = crate::Reg<lpi2c::LPI2C_SPEC>;
#[doc = "need des"]
pub mod lpi2c;
pub use crate::aes::{date, DATE};
