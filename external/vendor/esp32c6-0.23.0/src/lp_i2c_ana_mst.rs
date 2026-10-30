#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    i2c0_ctrl: I2C0_CTRL,
    i2c0_conf: I2C0_CONF,
    i2c0_data: I2C0_DATA,
    ana_conf1: ANA_CONF1,
    nouse: NOUSE,
    device_en: DEVICE_EN,
    _reserved6: [u8; 0x03e4],
    date: DATE,
}
impl RegisterBlock {
    #[doc = "0x00 - need_des"]
    #[inline(always)]
    pub const fn i2c0_ctrl(&self) -> &I2C0_CTRL {
        &self.i2c0_ctrl
    }
    #[doc = "0x04 - need_des"]
    #[inline(always)]
    pub const fn i2c0_conf(&self) -> &I2C0_CONF {
        &self.i2c0_conf
    }
    #[doc = "0x08 - need_des"]
    #[inline(always)]
    pub const fn i2c0_data(&self) -> &I2C0_DATA {
        &self.i2c0_data
    }
    #[doc = "0x0c - need_des"]
    #[inline(always)]
    pub const fn ana_conf1(&self) -> &ANA_CONF1 {
        &self.ana_conf1
    }
    #[doc = "0x10 - need_des"]
    #[inline(always)]
    pub const fn nouse(&self) -> &NOUSE {
        &self.nouse
    }
    #[doc = "0x14 - need_des"]
    #[inline(always)]
    pub const fn device_en(&self) -> &DEVICE_EN {
        &self.device_en
    }
    #[doc = "0x3fc - need_des"]
    #[inline(always)]
    pub const fn date(&self) -> &DATE {
        &self.date
    }
}
#[doc = "I2C0_CTRL (rw) register accessor: need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`i2c0_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`i2c0_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@i2c0_ctrl`] module"]
pub type I2C0_CTRL = crate::Reg<i2c0_ctrl::I2C0_CTRL_SPEC>;
#[doc = "need_des"]
pub mod i2c0_ctrl;
#[doc = "I2C0_CONF (rw) register accessor: need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`i2c0_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`i2c0_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@i2c0_conf`] module"]
pub type I2C0_CONF = crate::Reg<i2c0_conf::I2C0_CONF_SPEC>;
#[doc = "need_des"]
pub mod i2c0_conf;
#[doc = "I2C0_DATA (rw) register accessor: need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`i2c0_data::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`i2c0_data::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@i2c0_data`] module"]
pub type I2C0_DATA = crate::Reg<i2c0_data::I2C0_DATA_SPEC>;
#[doc = "need_des"]
pub mod i2c0_data;
#[doc = "ANA_CONF1 (rw) register accessor: need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`ana_conf1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ana_conf1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ana_conf1`] module"]
pub type ANA_CONF1 = crate::Reg<ana_conf1::ANA_CONF1_SPEC>;
#[doc = "need_des"]
pub mod ana_conf1;
#[doc = "NOUSE (rw) register accessor: need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`nouse::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`nouse::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@nouse`] module"]
pub type NOUSE = crate::Reg<nouse::NOUSE_SPEC>;
#[doc = "need_des"]
pub mod nouse;
#[doc = "DEVICE_EN (rw) register accessor: need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`device_en::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`device_en::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@device_en`] module"]
pub type DEVICE_EN = crate::Reg<device_en::DEVICE_EN_SPEC>;
#[doc = "need_des"]
pub mod device_en;
pub use crate::aes::{date, DATE};
