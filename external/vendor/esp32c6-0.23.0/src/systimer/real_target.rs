#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Cluster REAL_TARGET%s, containing REAL_TARGET?_LO, REAL_TARGET?_HI"]
pub struct REAL_TARGET {
    lo: LO,
    hi: HI,
}
impl REAL_TARGET {
    #[doc = "0x00 - system timer comp0 actual target value low register"]
    #[inline(always)]
    pub const fn lo(&self) -> &LO {
        &self.lo
    }
    #[doc = "0x04 - system timer comp0 actual target value high register"]
    #[inline(always)]
    pub const fn hi(&self) -> &HI {
        &self.hi
    }
}
#[doc = "LO (r) register accessor: system timer comp0 actual target value low register\n\nYou can [`read`](crate::Reg::read) this register and get [`lo::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@lo`] module"]
pub type LO = crate::Reg<lo::LO_SPEC>;
#[doc = "system timer comp0 actual target value low register"]
pub mod lo;
#[doc = "HI (r) register accessor: system timer comp0 actual target value high register\n\nYou can [`read`](crate::Reg::read) this register and get [`hi::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hi`] module"]
pub type HI = crate::Reg<hi::HI_SPEC>;
#[doc = "system timer comp0 actual target value high register"]
pub mod hi;
