#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Cluster TRGT%s, containing TARGET?_HI, TARGET?_LO"]
pub struct TRGT {
    hi: HI,
    lo: LO,
}
impl TRGT {
    #[doc = "0x00 - system timer comp0 value high register"]
    #[inline(always)]
    pub const fn hi(&self) -> &HI {
        &self.hi
    }
    #[doc = "0x04 - system timer comp0 value low register"]
    #[inline(always)]
    pub const fn lo(&self) -> &LO {
        &self.lo
    }
}
#[doc = "HI (rw) register accessor: system timer comp0 value high register\n\nYou can [`read`](crate::Reg::read) this register and get [`hi::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`hi::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hi`] module"]
pub type HI = crate::Reg<hi::HI_SPEC>;
#[doc = "system timer comp0 value high register"]
pub mod hi;
#[doc = "LO (rw) register accessor: system timer comp0 value low register\n\nYou can [`read`](crate::Reg::read) this register and get [`lo::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`lo::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@lo`] module"]
pub type LO = crate::Reg<lo::LO_SPEC>;
#[doc = "system timer comp0 value low register"]
pub mod lo;
