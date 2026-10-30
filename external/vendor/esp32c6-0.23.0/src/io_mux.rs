#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    pin_ctrl: PIN_CTRL,
    gpio: [GPIO; 31],
    _reserved2: [u8; 0x3c],
    modem_diag_en: MODEM_DIAG_EN,
    _reserved3: [u8; 0x3c],
    date: DATE,
}
impl RegisterBlock {
    #[doc = "0x00 - Clock Output Configuration Register"]
    #[inline(always)]
    pub const fn pin_ctrl(&self) -> &PIN_CTRL {
        &self.pin_ctrl
    }
    #[doc = "0x04..0x80 - IO MUX Configure Register for pad XTAL_32K_P"]
    #[inline(always)]
    pub const fn gpio(&self, n: usize) -> &GPIO {
        &self.gpio[n]
    }
    #[doc = "Iterator for array of:"]
    #[doc = "0x04..0x80 - IO MUX Configure Register for pad XTAL_32K_P"]
    #[inline(always)]
    pub fn gpio_iter(&self) -> impl Iterator<Item = &GPIO> {
        self.gpio.iter()
    }
    #[doc = "0xbc - GPIO MATRIX Configure Register for modem diag"]
    #[inline(always)]
    pub const fn modem_diag_en(&self) -> &MODEM_DIAG_EN {
        &self.modem_diag_en
    }
    #[doc = "0xfc - IO MUX Version Control Register"]
    #[inline(always)]
    pub const fn date(&self) -> &DATE {
        &self.date
    }
}
#[doc = "PIN_CTRL (rw) register accessor: Clock Output Configuration Register\n\nYou can [`read`](crate::Reg::read) this register and get [`pin_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pin_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pin_ctrl`] module"]
pub type PIN_CTRL = crate::Reg<pin_ctrl::PIN_CTRL_SPEC>;
#[doc = "Clock Output Configuration Register"]
pub mod pin_ctrl;
#[doc = "GPIO (rw) register accessor: IO MUX Configure Register for pad XTAL_32K_P\n\nYou can [`read`](crate::Reg::read) this register and get [`gpio::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`gpio::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@gpio`] module"]
pub type GPIO = crate::Reg<gpio::GPIO_SPEC>;
#[doc = "IO MUX Configure Register for pad XTAL_32K_P"]
pub mod gpio;
#[doc = "MODEM_DIAG_EN (rw) register accessor: GPIO MATRIX Configure Register for modem diag\n\nYou can [`read`](crate::Reg::read) this register and get [`modem_diag_en::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`modem_diag_en::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@modem_diag_en`] module"]
pub type MODEM_DIAG_EN = crate::Reg<modem_diag_en::MODEM_DIAG_EN_SPEC>;
#[doc = "GPIO MATRIX Configure Register for modem diag"]
pub mod modem_diag_en;
pub use crate::aes::{date, DATE};
