#[doc = "Register `L1_BYPASS_CACHE_CONF` reader"]
pub type R = crate::R<L1_BYPASS_CACHE_CONF_SPEC>;
#[doc = "Field `BYPASS_L1_ICACHE0_EN` reader - The bit is used to enable bypass L1-ICache0. 0: disable bypass, 1: enable bypass."]
pub type BYPASS_L1_ICACHE0_EN_R = crate::BitReader;
#[doc = "Field `BYPASS_L1_ICACHE1_EN` reader - The bit is used to enable bypass L1-ICache1. 0: disable bypass, 1: enable bypass."]
pub type BYPASS_L1_ICACHE1_EN_R = crate::BitReader;
#[doc = "Field `BYPASS_L1_ICACHE2_EN` reader - Reserved"]
pub type BYPASS_L1_ICACHE2_EN_R = crate::BitReader;
#[doc = "Field `BYPASS_L1_ICACHE3_EN` reader - Reserved"]
pub type BYPASS_L1_ICACHE3_EN_R = crate::BitReader;
#[doc = "Field `BYPASS_L1_DCACHE_EN` reader - The bit is used to enable bypass L1-DCache. 0: disable bypass, 1: enable bypass."]
pub type BYPASS_L1_DCACHE_EN_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - The bit is used to enable bypass L1-ICache0. 0: disable bypass, 1: enable bypass."]
    #[inline(always)]
    pub fn bypass_l1_icache0_en(&self) -> BYPASS_L1_ICACHE0_EN_R {
        BYPASS_L1_ICACHE0_EN_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The bit is used to enable bypass L1-ICache1. 0: disable bypass, 1: enable bypass."]
    #[inline(always)]
    pub fn bypass_l1_icache1_en(&self) -> BYPASS_L1_ICACHE1_EN_R {
        BYPASS_L1_ICACHE1_EN_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Reserved"]
    #[inline(always)]
    pub fn bypass_l1_icache2_en(&self) -> BYPASS_L1_ICACHE2_EN_R {
        BYPASS_L1_ICACHE2_EN_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Reserved"]
    #[inline(always)]
    pub fn bypass_l1_icache3_en(&self) -> BYPASS_L1_ICACHE3_EN_R {
        BYPASS_L1_ICACHE3_EN_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - The bit is used to enable bypass L1-DCache. 0: disable bypass, 1: enable bypass."]
    #[inline(always)]
    pub fn bypass_l1_dcache_en(&self) -> BYPASS_L1_DCACHE_EN_R {
        BYPASS_L1_DCACHE_EN_R::new(((self.bits >> 4) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L1_BYPASS_CACHE_CONF")
            .field("bypass_l1_icache0_en", &self.bypass_l1_icache0_en())
            .field("bypass_l1_icache1_en", &self.bypass_l1_icache1_en())
            .field("bypass_l1_icache2_en", &self.bypass_l1_icache2_en())
            .field("bypass_l1_icache3_en", &self.bypass_l1_icache3_en())
            .field("bypass_l1_dcache_en", &self.bypass_l1_dcache_en())
            .finish()
    }
}
#[doc = "Bypass Cache configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`l1_bypass_cache_conf::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L1_BYPASS_CACHE_CONF_SPEC;
impl crate::RegisterSpec for L1_BYPASS_CACHE_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l1_bypass_cache_conf::R`](R) reader structure"]
impl crate::Readable for L1_BYPASS_CACHE_CONF_SPEC {}
#[doc = "`reset()` method sets L1_BYPASS_CACHE_CONF to value 0"]
impl crate::Resettable for L1_BYPASS_CACHE_CONF_SPEC {}
