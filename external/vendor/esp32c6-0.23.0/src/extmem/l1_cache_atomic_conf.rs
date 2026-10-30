#[doc = "Register `L1_CACHE_ATOMIC_CONF` reader"]
pub type R = crate::R<L1_CACHE_ATOMIC_CONF_SPEC>;
#[doc = "Field `L1_CACHE_ATOMIC_EN` reader - The bit is used to enable atomic feature on L1-Cache when multiple cores access L1-Cache. 1: disable, 1: enable."]
pub type L1_CACHE_ATOMIC_EN_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - The bit is used to enable atomic feature on L1-Cache when multiple cores access L1-Cache. 1: disable, 1: enable."]
    #[inline(always)]
    pub fn l1_cache_atomic_en(&self) -> L1_CACHE_ATOMIC_EN_R {
        L1_CACHE_ATOMIC_EN_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L1_CACHE_ATOMIC_CONF")
            .field("l1_cache_atomic_en", &self.l1_cache_atomic_en())
            .finish()
    }
}
#[doc = "L1 Cache atomic feature configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`l1_cache_atomic_conf::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L1_CACHE_ATOMIC_CONF_SPEC;
impl crate::RegisterSpec for L1_CACHE_ATOMIC_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l1_cache_atomic_conf::R`](R) reader structure"]
impl crate::Readable for L1_CACHE_ATOMIC_CONF_SPEC {}
#[doc = "`reset()` method sets L1_CACHE_ATOMIC_CONF to value 0"]
impl crate::Resettable for L1_CACHE_ATOMIC_CONF_SPEC {}
