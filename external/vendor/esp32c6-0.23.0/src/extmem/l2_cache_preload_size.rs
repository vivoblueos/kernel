#[doc = "Register `L2_CACHE_PRELOAD_SIZE` reader"]
pub type R = crate::R<L2_CACHE_PRELOAD_SIZE_SPEC>;
#[doc = "Field `L2_CACHE_PRELOAD_SIZE` reader - Those bits are used to configure the size of the first section of prelock on L2-Cache, which should be used together with L2_CACHE_PRELOAD_ADDR_REG"]
pub type L2_CACHE_PRELOAD_SIZE_R = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:15 - Those bits are used to configure the size of the first section of prelock on L2-Cache, which should be used together with L2_CACHE_PRELOAD_ADDR_REG"]
    #[inline(always)]
    pub fn l2_cache_preload_size(&self) -> L2_CACHE_PRELOAD_SIZE_R {
        L2_CACHE_PRELOAD_SIZE_R::new((self.bits & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L2_CACHE_PRELOAD_SIZE")
            .field("l2_cache_preload_size", &self.l2_cache_preload_size())
            .finish()
    }
}
#[doc = "L2 Cache preload size configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`l2_cache_preload_size::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L2_CACHE_PRELOAD_SIZE_SPEC;
impl crate::RegisterSpec for L2_CACHE_PRELOAD_SIZE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l2_cache_preload_size::R`](R) reader structure"]
impl crate::Readable for L2_CACHE_PRELOAD_SIZE_SPEC {}
#[doc = "`reset()` method sets L2_CACHE_PRELOAD_SIZE to value 0"]
impl crate::Resettable for L2_CACHE_PRELOAD_SIZE_SPEC {}
