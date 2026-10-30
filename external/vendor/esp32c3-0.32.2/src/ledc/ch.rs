#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Cluster CH%s, containing CH?_CONF0, CH?_HPOINT, CH?_DUTY, CH?_CONF1, CH?_DUTY_R"]
pub struct CH {
    conf0: CONF0,
    hpoint: HPOINT,
    duty: DUTY,
    conf1: CONF1,
    duty_r: DUTY_R,
}
impl CH {
    #[doc = "0x00 - LEDC_LSCH0_CONF0."]
    #[inline(always)]
    pub const fn conf0(&self) -> &CONF0 {
        &self.conf0
    }
    #[doc = "0x04 - LEDC_LSCH0_HPOINT."]
    #[inline(always)]
    pub const fn hpoint(&self) -> &HPOINT {
        &self.hpoint
    }
    #[doc = "0x08 - LEDC_LSCH0_DUTY."]
    #[inline(always)]
    pub const fn duty(&self) -> &DUTY {
        &self.duty
    }
    #[doc = "0x0c - LEDC_LSCH0_CONF1."]
    #[inline(always)]
    pub const fn conf1(&self) -> &CONF1 {
        &self.conf1
    }
    #[doc = "0x10 - LEDC_LSCH0_DUTY_R."]
    #[inline(always)]
    pub const fn duty_r(&self) -> &DUTY_R {
        &self.duty_r
    }
}
#[doc = "CONF0 (rw) register accessor: LEDC_LSCH0_CONF0.\n\nYou can [`read`](crate::Reg::read) this register and get [`conf0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@conf0`] module"]
pub type CONF0 = crate::Reg<conf0::CONF0_SPEC>;
#[doc = "LEDC_LSCH0_CONF0."]
pub mod conf0;
#[doc = "HPOINT (rw) register accessor: LEDC_LSCH0_HPOINT.\n\nYou can [`read`](crate::Reg::read) this register and get [`hpoint::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`hpoint::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@hpoint`] module"]
pub type HPOINT = crate::Reg<hpoint::HPOINT_SPEC>;
#[doc = "LEDC_LSCH0_HPOINT."]
pub mod hpoint;
#[doc = "DUTY (rw) register accessor: LEDC_LSCH0_DUTY.\n\nYou can [`read`](crate::Reg::read) this register and get [`duty::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`duty::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@duty`] module"]
pub type DUTY = crate::Reg<duty::DUTY_SPEC>;
#[doc = "LEDC_LSCH0_DUTY."]
pub mod duty;
#[doc = "CONF1 (rw) register accessor: LEDC_LSCH0_CONF1.\n\nYou can [`read`](crate::Reg::read) this register and get [`conf1::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf1::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@conf1`] module"]
pub type CONF1 = crate::Reg<conf1::CONF1_SPEC>;
#[doc = "LEDC_LSCH0_CONF1."]
pub mod conf1;
#[doc = "DUTY_R (r) register accessor: LEDC_LSCH0_DUTY_R.\n\nYou can [`read`](crate::Reg::read) this register and get [`duty_r::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@duty_r`] module"]
pub type DUTY_R = crate::Reg<duty_r::DUTY_R_SPEC>;
#[doc = "LEDC_LSCH0_DUTY_R."]
pub mod duty_r;
