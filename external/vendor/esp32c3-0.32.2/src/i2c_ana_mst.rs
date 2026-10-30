#[repr(C)]
#[cfg_attr(feature = "impl-register-debug", derive(Debug))]
#[doc = "Register block"]
pub struct RegisterBlock {
    ana_conf0: ANA_CONF0,
    ana_config: ANA_CONFIG,
    ana_config2: ANA_CONFIG2,
}
impl RegisterBlock {
    #[doc = "0x00 - ANA_CONF0 register"]
    #[inline(always)]
    pub const fn ana_conf0(&self) -> &ANA_CONF0 {
        &self.ana_conf0
    }
    #[doc = "0x04 - ANA_CONFIG register"]
    #[inline(always)]
    pub const fn ana_config(&self) -> &ANA_CONFIG {
        &self.ana_config
    }
    #[doc = "0x08 - ANA_CONFIG2 register"]
    #[inline(always)]
    pub const fn ana_config2(&self) -> &ANA_CONFIG2 {
        &self.ana_config2
    }
}
#[doc = "ANA_CONF0 (rw) register accessor: ANA_CONF0 register\n\nYou can [`read`](crate::Reg::read) this register and get [`ana_conf0::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ana_conf0::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ana_conf0`] module"]
pub type ANA_CONF0 = crate::Reg<ana_conf0::ANA_CONF0_SPEC>;
#[doc = "ANA_CONF0 register"]
pub mod ana_conf0;
#[doc = "ANA_CONFIG (rw) register accessor: ANA_CONFIG register\n\nYou can [`read`](crate::Reg::read) this register and get [`ana_config::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ana_config::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ana_config`] module"]
pub type ANA_CONFIG = crate::Reg<ana_config::ANA_CONFIG_SPEC>;
#[doc = "ANA_CONFIG register"]
pub mod ana_config;
#[doc = "ANA_CONFIG2 (rw) register accessor: ANA_CONFIG2 register\n\nYou can [`read`](crate::Reg::read) this register and get [`ana_config2::R`]. You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`ana_config2::W`]. You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api).\n\nFor information about available fields see [`mod@ana_config2`] module"]
pub type ANA_CONFIG2 = crate::Reg<ana_config2::ANA_CONFIG2_SPEC>;
#[doc = "ANA_CONFIG2 register"]
pub mod ana_config2;
