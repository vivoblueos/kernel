#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    _reserved0: [u8; 0xf0],
    tx_interp_ctrl: TX_INTERP_CTRL,
}
impl RegisterBlock {
    #[doc = "0xf0 - FE2 TX Interpolation Control Register"]
    #[inline(always)]
    pub const fn tx_interp_ctrl(&self) -> &TX_INTERP_CTRL {
        &self.tx_interp_ctrl
    }
}
#[doc = "TX_INTERP_CTRL (rw) register accessor: FE2 TX Interpolation Control Register\n\nYou can [`read`](crate::Reg::read) this register and get [`tx_interp_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`tx_interp_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@tx_interp_ctrl`] module"]
pub type TX_INTERP_CTRL = crate::Reg<tx_interp_ctrl::TX_INTERP_CTRL_SPEC>;
#[doc = "FE2 TX Interpolation Control Register"]
pub mod tx_interp_ctrl;
