#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Cluster TIMER%s, containing TIMER?_CONF, TIMER?_VALUE"]
pub struct TIMER {
    conf: CONF,
    value: VALUE,
}
impl TIMER {
    #[doc = "0x00 - LEDC_LSTIMER0_CONF."]
    #[inline(always)]
    pub const fn conf(&self) -> &CONF {
        &self.conf
    }
    #[doc = "0x04 - LEDC_LSTIMER0_VALUE."]
    #[inline(always)]
    pub const fn value(&self) -> &VALUE {
        &self.value
    }
}
#[doc = "CONF (rw) register accessor: LEDC_LSTIMER0_CONF.\n\nYou can [`read`](crate::Reg::read) this register and get [`conf::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`conf::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@conf`] module"]
pub type CONF = crate::Reg<conf::CONF_SPEC>;
#[doc = "LEDC_LSTIMER0_CONF."]
pub mod conf;
#[doc = "VALUE (r) register accessor: LEDC_LSTIMER0_VALUE.\n\nYou can [`read`](crate::Reg::read) this register and get [`value::R`]. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@value`] module"]
pub type VALUE = crate::Reg<value::VALUE_SPEC>;
#[doc = "LEDC_LSTIMER0_VALUE."]
pub mod value;
