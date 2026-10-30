#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    _reserved0: [u8; 0xd4],
    nrxpd_ctrl: NRXPD_CTRL,
}
impl RegisterBlock {
    #[doc = "0xd4 - NRX Power Down Control Register"]
    #[inline(always)]
    pub const fn nrxpd_ctrl(&self) -> &NRXPD_CTRL {
        &self.nrxpd_ctrl
    }
}
#[doc = "NRXPD_CTRL (rw) register accessor: NRX Power Down Control Register\n\nYou can [`read`](crate::Reg::read) this register and get [`nrxpd_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`nrxpd_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@nrxpd_ctrl`] module"]
pub type NRXPD_CTRL = crate::Reg<nrxpd_ctrl::NRXPD_CTRL_SPEC>;
#[doc = "NRX Power Down Control Register"]
pub mod nrxpd_ctrl;
