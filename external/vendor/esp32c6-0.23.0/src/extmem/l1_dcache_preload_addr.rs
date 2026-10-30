#[doc = "Register `L1_DCACHE_PRELOAD_ADDR` reader"]
pub type R = crate::R<L1_DCACHE_PRELOAD_ADDR_SPEC>;
#[doc = "Register `L1_DCACHE_PRELOAD_ADDR` writer"]
pub type W = crate::W<L1_DCACHE_PRELOAD_ADDR_SPEC>;
#[doc = "Field `L1_CACHE_PRELOAD_ADDR` reader - Those bits are used to configure the start virtual address of preload on L1-Cache, which should be used together with L1_CACHE_PRELOAD_SIZE_REG"]
pub type L1_CACHE_PRELOAD_ADDR_R = crate::FieldReader<u32>;
#[doc = "Field `L1_CACHE_PRELOAD_ADDR` writer - Those bits are used to configure the start virtual address of preload on L1-Cache, which should be used together with L1_CACHE_PRELOAD_SIZE_REG"]
pub type L1_CACHE_PRELOAD_ADDR_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - Those bits are used to configure the start virtual address of preload on L1-Cache, which should be used together with L1_CACHE_PRELOAD_SIZE_REG"]
    #[inline(always)]
    pub fn l1_cache_preload_addr(&self) -> L1_CACHE_PRELOAD_ADDR_R {
        L1_CACHE_PRELOAD_ADDR_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L1_DCACHE_PRELOAD_ADDR")
            .field("l1_cache_preload_addr", &self.l1_cache_preload_addr())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - Those bits are used to configure the start virtual address of preload on L1-Cache, which should be used together with L1_CACHE_PRELOAD_SIZE_REG"]
    #[inline(always)]
    pub fn l1_cache_preload_addr(
        &mut self,
    ) -> L1_CACHE_PRELOAD_ADDR_W<'_, L1_DCACHE_PRELOAD_ADDR_SPEC> {
        L1_CACHE_PRELOAD_ADDR_W::new(self, 0)
    }
}
#[doc = "L1 Cache preload address configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`l1_dcache_preload_addr::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`l1_dcache_preload_addr::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L1_DCACHE_PRELOAD_ADDR_SPEC;
impl crate::RegisterSpec for L1_DCACHE_PRELOAD_ADDR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l1_dcache_preload_addr::R`](R) reader structure"]
impl crate::Readable for L1_DCACHE_PRELOAD_ADDR_SPEC {}
#[doc = "`write(|w| ..)` method takes [`l1_dcache_preload_addr::W`](W) writer structure"]
impl crate::Writable for L1_DCACHE_PRELOAD_ADDR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets L1_DCACHE_PRELOAD_ADDR to value 0"]
impl crate::Resettable for L1_DCACHE_PRELOAD_ADDR_SPEC {}
