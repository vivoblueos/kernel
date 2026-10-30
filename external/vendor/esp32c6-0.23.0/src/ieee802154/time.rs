#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Cluster TIME%s, containing TIME?_THRESHOLD, TIME?_VALUE"]
pub struct TIME {
    threshold: THRESHOLD,
    value: VALUE,
}
impl TIME {
    #[doc = "0x00 - "]
    #[inline(always)]
    pub const fn threshold(&self) -> &THRESHOLD {
        &self.threshold
    }
    #[doc = "0x04 - "]
    #[inline(always)]
    pub const fn value(&self) -> &VALUE {
        &self.value
    }
}
#[doc = "THRESHOLD (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`threshold::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`threshold::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@threshold`] module"]
pub type THRESHOLD = crate::Reg<threshold::THRESHOLD_SPEC>;
#[doc = ""]
pub mod threshold;
#[doc = "VALUE (rw) register accessor: \n\nYou can [`read`](crate::Reg::read) this register and get [`value::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`value::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@value`] module"]
pub type VALUE = crate::Reg<value::VALUE_SPEC>;
#[doc = ""]
pub mod value;
