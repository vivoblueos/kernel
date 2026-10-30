#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Cluster DMA_APBPERI%s, containing DMA_APBPERI*_PMS_CONSTRAIN_0, DMA_APBPERI*_PMS_CONSTRAIN_1"]
pub struct DMA_APBPERI {
    pms_constrain_0: PMS_CONSTRAIN_0,
    pms_constrain_1: PMS_CONSTRAIN_1,
}
impl DMA_APBPERI {
    #[doc = "0x00 - SENSITIVE_DMA_APBPERI_SPI2_PMS_CONSTRAIN_0_REG"]
    #[inline(always)]
    pub const fn pms_constrain_0(&self) -> &PMS_CONSTRAIN_0 {
        &self.pms_constrain_0
    }
    #[doc = "0x04 - SENSITIVE_DMA_APBPERI_SPI2_PMS_CONSTRAIN_1_REG"]
    #[inline(always)]
    pub const fn pms_constrain_1(&self) -> &PMS_CONSTRAIN_1 {
        &self.pms_constrain_1
    }
}
#[doc = "PMS_CONSTRAIN_0 (rw) register accessor: SENSITIVE_DMA_APBPERI_SPI2_PMS_CONSTRAIN_0_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`pms_constrain_0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pms_constrain_0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pms_constrain_0`] module"]
pub type PMS_CONSTRAIN_0 = crate::Reg<pms_constrain_0::PMS_CONSTRAIN_0_SPEC>;
#[doc = "SENSITIVE_DMA_APBPERI_SPI2_PMS_CONSTRAIN_0_REG"]
pub mod pms_constrain_0;
#[doc = "PMS_CONSTRAIN_1 (rw) register accessor: SENSITIVE_DMA_APBPERI_SPI2_PMS_CONSTRAIN_1_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`pms_constrain_1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`pms_constrain_1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@pms_constrain_1`] module"]
pub type PMS_CONSTRAIN_1 = crate::Reg<pms_constrain_1::PMS_CONSTRAIN_1_SPEC>;
#[doc = "SENSITIVE_DMA_APBPERI_SPI2_PMS_CONSTRAIN_1_REG"]
pub mod pms_constrain_1;
