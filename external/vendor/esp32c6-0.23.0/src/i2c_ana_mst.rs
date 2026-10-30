#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    i2c_ctrl: [I2C_CTRL; 2],
    i2c0_conf: I2C0_CONF,
    i2c1_conf: I2C1_CONF,
    burst_conf: BURST_CONF,
    burst_status: BURST_STATUS,
    ana_conf0: ANA_CONF0,
    ana_conf1: ANA_CONF1,
    ana_conf2: ANA_CONF2,
    i2c_ctrl1: [I2C_CTRL1; 2],
    _reserved9: [u8; 0x08],
    date: DATE,
}
impl RegisterBlock {
    #[doc = "0x00..0x08 - I2C%s_CTRL register"]
    #[inline(always)]
    pub const fn i2c_ctrl(&self, n: usize) -> &I2C_CTRL {
        &self.i2c_ctrl[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x00..0x08 - I2C%s_CTRL register"]
    #[inline(always)]
    pub fn i2c_ctrl_iter(&self) -> impl Iterator<Item = &I2C_CTRL> {
        self.i2c_ctrl.iter()
    }
    #[doc = "0x00 - I2C0_CTRL register"]
    #[inline(always)]
    pub const fn i2c0_ctrl(&self) -> &I2C_CTRL {
        self.i2c_ctrl(0)
    }
    #[doc = "0x04 - I2C1_CTRL register"]
    #[inline(always)]
    pub const fn i2c1_ctrl(&self) -> &I2C_CTRL {
        self.i2c_ctrl(1)
    }
    #[doc = "0x08 - I2C0_CONF register"]
    #[inline(always)]
    pub const fn i2c0_conf(&self) -> &I2C0_CONF {
        &self.i2c0_conf
    }
    #[doc = "0x0c - I2C1_CONF register"]
    #[inline(always)]
    pub const fn i2c1_conf(&self) -> &I2C1_CONF {
        &self.i2c1_conf
    }
    #[doc = "0x10 - BURST_CONF register"]
    #[inline(always)]
    pub const fn burst_conf(&self) -> &BURST_CONF {
        &self.burst_conf
    }
    #[doc = "0x14 - BURST_STATUS register"]
    #[inline(always)]
    pub const fn burst_status(&self) -> &BURST_STATUS {
        &self.burst_status
    }
    #[doc = "0x18 - ANA_CONF0 register"]
    #[inline(always)]
    pub const fn ana_conf0(&self) -> &ANA_CONF0 {
        &self.ana_conf0
    }
    #[doc = "0x1c - ANA_CONF1 register"]
    #[inline(always)]
    pub const fn ana_conf1(&self) -> &ANA_CONF1 {
        &self.ana_conf1
    }
    #[doc = "0x20 - ANA_CONF2 register"]
    #[inline(always)]
    pub const fn ana_conf2(&self) -> &ANA_CONF2 {
        &self.ana_conf2
    }
    #[doc = "0x24..0x2c - I2C%s_CTRL1 register"]
    #[inline(always)]
    pub const fn i2c_ctrl1(&self, n: usize) -> &I2C_CTRL1 {
        &self.i2c_ctrl1[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x24..0x2c - I2C%s_CTRL1 register"]
    #[inline(always)]
    pub fn i2c_ctrl1_iter(&self) -> impl Iterator<Item = &I2C_CTRL1> {
        self.i2c_ctrl1.iter()
    }
    #[doc = "0x24 - I2C0_CTRL1 register"]
    #[inline(always)]
    pub const fn i2c0_ctrl1(&self) -> &I2C_CTRL1 {
        self.i2c_ctrl1(0)
    }
    #[doc = "0x28 - I2C1_CTRL1 register"]
    #[inline(always)]
    pub const fn i2c1_ctrl1(&self) -> &I2C_CTRL1 {
        self.i2c_ctrl1(1)
    }
    #[doc = "0x34 - DATE register"]
    #[inline(always)]
    pub const fn date(&self) -> &DATE {
        &self.date
    }
}
#[doc = "I2C_CTRL (rw) register accessor: I2C%s_CTRL register\n\nYou can [`read`](crate::Reg::read) this register and get [`i2c_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`i2c_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@i2c_ctrl`] module"]
pub type I2C_CTRL = crate::Reg<i2c_ctrl::I2C_CTRL_SPEC>;
#[doc = "I2C%s_CTRL register"]
pub mod i2c_ctrl;
#[doc = "I2C0_CONF (rw) register accessor: I2C0_CONF register\n\nYou can [`read`](crate::Reg::read) this register and get [`i2c0_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`i2c0_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@i2c0_conf`] module"]
pub type I2C0_CONF = crate::Reg<i2c0_conf::I2C0_CONF_SPEC>;
#[doc = "I2C0_CONF register"]
pub mod i2c0_conf;
#[doc = "I2C1_CONF (rw) register accessor: I2C1_CONF register\n\nYou can [`read`](crate::Reg::read) this register and get [`i2c1_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`i2c1_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@i2c1_conf`] module"]
pub type I2C1_CONF = crate::Reg<i2c1_conf::I2C1_CONF_SPEC>;
#[doc = "I2C1_CONF register"]
pub mod i2c1_conf;
#[doc = "BURST_CONF (rw) register accessor: BURST_CONF register\n\nYou can [`read`](crate::Reg::read) this register and get [`burst_conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`burst_conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@burst_conf`] module"]
pub type BURST_CONF = crate::Reg<burst_conf::BURST_CONF_SPEC>;
#[doc = "BURST_CONF register"]
pub mod burst_conf;
#[doc = "BURST_STATUS (rw) register accessor: BURST_STATUS register\n\nYou can [`read`](crate::Reg::read) this register and get [`burst_status::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`burst_status::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@burst_status`] module"]
pub type BURST_STATUS = crate::Reg<burst_status::BURST_STATUS_SPEC>;
#[doc = "BURST_STATUS register"]
pub mod burst_status;
#[doc = "ANA_CONF0 (rw) register accessor: ANA_CONF0 register\n\nYou can [`read`](crate::Reg::read) this register and get [`ana_conf0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ana_conf0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ana_conf0`] module"]
pub type ANA_CONF0 = crate::Reg<ana_conf0::ANA_CONF0_SPEC>;
#[doc = "ANA_CONF0 register"]
pub mod ana_conf0;
#[doc = "ANA_CONF1 (rw) register accessor: ANA_CONF1 register\n\nYou can [`read`](crate::Reg::read) this register and get [`ana_conf1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ana_conf1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ana_conf1`] module"]
pub type ANA_CONF1 = crate::Reg<ana_conf1::ANA_CONF1_SPEC>;
#[doc = "ANA_CONF1 register"]
pub mod ana_conf1;
#[doc = "ANA_CONF2 (rw) register accessor: ANA_CONF2 register\n\nYou can [`read`](crate::Reg::read) this register and get [`ana_conf2::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ana_conf2::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ana_conf2`] module"]
pub type ANA_CONF2 = crate::Reg<ana_conf2::ANA_CONF2_SPEC>;
#[doc = "ANA_CONF2 register"]
pub mod ana_conf2;
#[doc = "I2C_CTRL1 (rw) register accessor: I2C%s_CTRL1 register\n\nYou can [`read`](crate::Reg::read) this register and get [`i2c_ctrl1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`i2c_ctrl1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@i2c_ctrl1`] module"]
pub type I2C_CTRL1 = crate::Reg<i2c_ctrl1::I2C_CTRL1_SPEC>;
#[doc = "I2C%s_CTRL1 register"]
pub mod i2c_ctrl1;
pub use crate::aes::{date, DATE};
