#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Cluster INT_CH%s, containing INT_RAW_CH?, INT_ST_CH?, INT_ENA_CH?, INT_CLR_CH?"]
pub struct INT_CH {
    raw: RAW,
    st: ST,
    ena: ENA,
    clr: CLR,
}
impl INT_CH {
    #[doc = "0x00 - DMA_INT_RAW_CH0_REG."]
    #[inline(always)]
    pub const fn raw(&self) -> &RAW {
        &self.raw
    }
    #[doc = "0x04 - DMA_INT_ST_CH0_REG."]
    #[inline(always)]
    pub const fn st(&self) -> &ST {
        &self.st
    }
    #[doc = "0x08 - DMA_INT_ENA_CH0_REG."]
    #[inline(always)]
    pub const fn ena(&self) -> &ENA {
        &self.ena
    }
    #[doc = "0x0c - DMA_INT_CLR_CH0_REG."]
    #[inline(always)]
    pub const fn clr(&self) -> &CLR {
        &self.clr
    }
}
#[doc = "RAW (rw) register accessor: DMA_INT_RAW_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`raw::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`raw::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@raw`] module"]
pub type RAW = crate::Reg<raw::RAW_SPEC>;
#[doc = "DMA_INT_RAW_CH0_REG."]
pub mod raw;
#[doc = "ST (r) register accessor: DMA_INT_ST_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`st::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@st`] module"]
pub type ST = crate::Reg<st::ST_SPEC>;
#[doc = "DMA_INT_ST_CH0_REG."]
pub mod st;
#[doc = "ENA (rw) register accessor: DMA_INT_ENA_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`ena::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ena::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ena`] module"]
pub type ENA = crate::Reg<ena::ENA_SPEC>;
#[doc = "DMA_INT_ENA_CH0_REG."]
pub mod ena;
#[doc = "CLR (w) register accessor: DMA_INT_CLR_CH0_REG.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`clr::W`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@clr`] module"]
pub type CLR = crate::Reg<clr::CLR_SPEC>;
#[doc = "DMA_INT_CLR_CH0_REG."]
pub mod clr;
