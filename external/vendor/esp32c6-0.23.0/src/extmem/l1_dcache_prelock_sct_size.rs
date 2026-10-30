#[doc = "Register `L1_DCACHE_PRELOCK_SCT_SIZE` reader"]
pub type R = crate::R<L1_DCACHE_PRELOCK_SCT_SIZE_SPEC>;
#[doc = "Register `L1_DCACHE_PRELOCK_SCT_SIZE` writer"]
pub type W = crate::W<L1_DCACHE_PRELOCK_SCT_SIZE_SPEC>;
#[doc = "Field `L1_CACHE_PRELOCK_SCT0_SIZE` reader - Those bits are used to configure the size of the first section of prelock on L1-Cache, which should be used together with L1_CACHE_PRELOCK_SCT0_ADDR_REG"]
pub type L1_CACHE_PRELOCK_SCT0_SIZE_R = crate::FieldReader<u16>;
#[doc = "Field `L1_CACHE_PRELOCK_SCT0_SIZE` writer - Those bits are used to configure the size of the first section of prelock on L1-Cache, which should be used together with L1_CACHE_PRELOCK_SCT0_ADDR_REG"]
pub type L1_CACHE_PRELOCK_SCT0_SIZE_W<'a, REG> = crate::FieldWriter<'a, REG, 14, u16>;
#[doc = "Field `L1_CACHE_PRELOCK_SCT1_SIZE` reader - Those bits are used to configure the size of the second section of prelock on L1-Cache, which should be used together with L1_CACHE_PRELOCK_SCT1_ADDR_REG"]
pub type L1_CACHE_PRELOCK_SCT1_SIZE_R = crate::FieldReader<u16>;
#[doc = "Field `L1_CACHE_PRELOCK_SCT1_SIZE` writer - Those bits are used to configure the size of the second section of prelock on L1-Cache, which should be used together with L1_CACHE_PRELOCK_SCT1_ADDR_REG"]
pub type L1_CACHE_PRELOCK_SCT1_SIZE_W<'a, REG> = crate::FieldWriter<'a, REG, 14, u16>;
impl R {
    #[doc = "Bits 0:13 - Those bits are used to configure the size of the first section of prelock on L1-Cache, which should be used together with L1_CACHE_PRELOCK_SCT0_ADDR_REG"]
    #[inline(always)]
    pub fn l1_cache_prelock_sct0_size(&self) -> L1_CACHE_PRELOCK_SCT0_SIZE_R {
        L1_CACHE_PRELOCK_SCT0_SIZE_R::new((self.bits & 0x3fff) as u16)
    }
    #[doc = "Bits 16:29 - Those bits are used to configure the size of the second section of prelock on L1-Cache, which should be used together with L1_CACHE_PRELOCK_SCT1_ADDR_REG"]
    #[inline(always)]
    pub fn l1_cache_prelock_sct1_size(&self) -> L1_CACHE_PRELOCK_SCT1_SIZE_R {
        L1_CACHE_PRELOCK_SCT1_SIZE_R::new(((self.bits >> 16) & 0x3fff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L1_DCACHE_PRELOCK_SCT_SIZE")
            .field(
                "l1_cache_prelock_sct0_size",
                &self.l1_cache_prelock_sct0_size(),
            )
            .field(
                "l1_cache_prelock_sct1_size",
                &self.l1_cache_prelock_sct1_size(),
            )
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:13 - Those bits are used to configure the size of the first section of prelock on L1-Cache, which should be used together with L1_CACHE_PRELOCK_SCT0_ADDR_REG"]
    #[inline(always)]
    pub fn l1_cache_prelock_sct0_size(
        &mut self,
    ) -> L1_CACHE_PRELOCK_SCT0_SIZE_W<'_, L1_DCACHE_PRELOCK_SCT_SIZE_SPEC> {
        L1_CACHE_PRELOCK_SCT0_SIZE_W::new(self, 0)
    }
    #[doc = "Bits 16:29 - Those bits are used to configure the size of the second section of prelock on L1-Cache, which should be used together with L1_CACHE_PRELOCK_SCT1_ADDR_REG"]
    #[inline(always)]
    pub fn l1_cache_prelock_sct1_size(
        &mut self,
    ) -> L1_CACHE_PRELOCK_SCT1_SIZE_W<'_, L1_DCACHE_PRELOCK_SCT_SIZE_SPEC> {
        L1_CACHE_PRELOCK_SCT1_SIZE_W::new(self, 16)
    }
}
#[doc = "L1 Cache prelock section size configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`l1_dcache_prelock_sct_size::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`l1_dcache_prelock_sct_size::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L1_DCACHE_PRELOCK_SCT_SIZE_SPEC;
impl crate::RegisterSpec for L1_DCACHE_PRELOCK_SCT_SIZE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l1_dcache_prelock_sct_size::R`](R) reader structure"]
impl crate::Readable for L1_DCACHE_PRELOCK_SCT_SIZE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`l1_dcache_prelock_sct_size::W`](W) writer structure"]
impl crate::Writable for L1_DCACHE_PRELOCK_SCT_SIZE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets L1_DCACHE_PRELOCK_SCT_SIZE to value 0x3fff_3fff"]
impl crate::Resettable for L1_DCACHE_PRELOCK_SCT_SIZE_SPEC {
    const RESET_VALUE: u32 = 0x3fff_3fff;
}
