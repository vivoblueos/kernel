#[doc = "Register `L2_BYPASS_CACHE_CONF` reader"]
pub type R = crate::R<L2_BYPASS_CACHE_CONF_SPEC>;
#[doc = "Field `BYPASS_L2_CACHE_EN` reader - The bit is used to enable bypass L2-Cache. 0: disable bypass, 1: enable bypass."]
pub type BYPASS_L2_CACHE_EN_R = crate::BitReader;
impl R {
    #[doc = "Bit 5 - The bit is used to enable bypass L2-Cache. 0: disable bypass, 1: enable bypass."]
    #[inline(always)]
    pub fn bypass_l2_cache_en(&self) -> BYPASS_L2_CACHE_EN_R {
        BYPASS_L2_CACHE_EN_R::new(((self.bits >> 5) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L2_BYPASS_CACHE_CONF")
            .field("bypass_l2_cache_en", &self.bypass_l2_cache_en())
            .finish()
    }
}
#[doc = "Bypass Cache configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`l2_bypass_cache_conf::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L2_BYPASS_CACHE_CONF_SPEC;
impl crate::RegisterSpec for L2_BYPASS_CACHE_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l2_bypass_cache_conf::R`](R) reader structure"]
impl crate::Readable for L2_BYPASS_CACHE_CONF_SPEC {}
#[doc = "`reset()` method sets L2_BYPASS_CACHE_CONF to value 0"]
impl crate::Resettable for L2_BYPASS_CACHE_CONF_SPEC {}
