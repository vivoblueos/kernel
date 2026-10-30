#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    _reserved0: [u8; 0x90],
    gen_ctrl: GEN_CTRL,
}
impl RegisterBlock {
    #[doc = "0x90 - FE General Control Register"]
    #[inline(always)]
    pub const fn gen_ctrl(&self) -> &GEN_CTRL {
        &self.gen_ctrl
    }
}
#[doc = "GEN_CTRL (rw) register accessor: FE General Control Register\n\nYou can [`read`](crate::Reg::read) this register and get [`gen_ctrl::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`gen_ctrl::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@gen_ctrl`] module"]
pub type GEN_CTRL = crate::Reg<gen_ctrl::GEN_CTRL_SPEC>;
#[doc = "FE General Control Register"]
pub mod gen_ctrl;
