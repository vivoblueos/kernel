#[doc = "Register `L1_DCACHE_PRELOAD_SIZE` reader"]
pub type R = crate::R<L1_DCACHE_PRELOAD_SIZE_SPEC>;
#[doc = "Register `L1_DCACHE_PRELOAD_SIZE` writer"]
pub type W = crate::W<L1_DCACHE_PRELOAD_SIZE_SPEC>;
#[doc = "Field `L1_CACHE_PRELOAD_SIZE` reader - Those bits are used to configure the size of the first section of prelock on L1-Cache, which should be used together with L1_CACHE_PRELOAD_ADDR_REG"]
pub type L1_CACHE_PRELOAD_SIZE_R = crate::FieldReader<u16>;
#[doc = "Field `L1_CACHE_PRELOAD_SIZE` writer - Those bits are used to configure the size of the first section of prelock on L1-Cache, which should be used together with L1_CACHE_PRELOAD_ADDR_REG"]
pub type L1_CACHE_PRELOAD_SIZE_W<'a, REG> = crate::FieldWriter<'a, REG, 14, u16>;
impl R {
    #[doc = "Bits 0:13 - Those bits are used to configure the size of the first section of prelock on L1-Cache, which should be used together with L1_CACHE_PRELOAD_ADDR_REG"]
    #[inline(always)]
    pub fn l1_cache_preload_size(&self) -> L1_CACHE_PRELOAD_SIZE_R {
        L1_CACHE_PRELOAD_SIZE_R::new((self.bits & 0x3fff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L1_DCACHE_PRELOAD_SIZE")
            .field("l1_cache_preload_size", &self.l1_cache_preload_size())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:13 - Those bits are used to configure the size of the first section of prelock on L1-Cache, which should be used together with L1_CACHE_PRELOAD_ADDR_REG"]
    #[inline(always)]
    pub fn l1_cache_preload_size(
        &mut self,
    ) -> L1_CACHE_PRELOAD_SIZE_W<'_, L1_DCACHE_PRELOAD_SIZE_SPEC> {
        L1_CACHE_PRELOAD_SIZE_W::new(self, 0)
    }
}
#[doc = "L1 Cache preload size configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`l1_dcache_preload_size::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`l1_dcache_preload_size::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L1_DCACHE_PRELOAD_SIZE_SPEC;
impl crate::RegisterSpec for L1_DCACHE_PRELOAD_SIZE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l1_dcache_preload_size::R`](R) reader structure"]
impl crate::Readable for L1_DCACHE_PRELOAD_SIZE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`l1_dcache_preload_size::W`](W) writer structure"]
impl crate::Writable for L1_DCACHE_PRELOAD_SIZE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets L1_DCACHE_PRELOAD_SIZE to value 0"]
impl crate::Resettable for L1_DCACHE_PRELOAD_SIZE_SPEC {}
