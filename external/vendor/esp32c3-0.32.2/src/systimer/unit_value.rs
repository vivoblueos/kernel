#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Cluster UNIT%s_VALUE, containing UNIT?_VALUE_HI, UNIT?_VALUE_LO"]
pub struct UNIT_VALUE {
    hi: HI,
    lo: LO,
}
impl UNIT_VALUE {
    #[doc = "0x00 - SYSTIMER_UNIT0_VALUE_HI."]
    #[inline(always)]
    pub const fn hi(&self) -> &HI {
        &self.hi
    }
    #[doc = "0x04 - SYSTIMER_UNIT0_VALUE_LO."]
    #[inline(always)]
    pub const fn lo(&self) -> &LO {
        &self.lo
    }
}
#[doc = "HI (r) register accessor: SYSTIMER_UNIT0_VALUE_HI.\n\nYou can [`read`](crate::Reg::read) this register and get [`hi::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hi`] module"]
pub type HI = crate::Reg<hi::HI_SPEC>;
#[doc = "SYSTIMER_UNIT0_VALUE_HI."]
pub mod hi;
#[doc = "LO (r) register accessor: SYSTIMER_UNIT0_VALUE_LO.\n\nYou can [`read`](crate::Reg::read) this register and get [`lo::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@lo`] module"]
pub type LO = crate::Reg<lo::LO_SPEC>;
#[doc = "SYSTIMER_UNIT0_VALUE_LO."]
pub mod lo;
