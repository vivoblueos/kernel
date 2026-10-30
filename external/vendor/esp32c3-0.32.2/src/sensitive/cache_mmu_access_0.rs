#[doc = "Register `CACHE_MMU_ACCESS_0` reader"]
pub type R = crate::R<CACHE_MMU_ACCESS_0_SPEC>;
#[doc = "Register `CACHE_MMU_ACCESS_0` writer"]
pub type W = crate::W<CACHE_MMU_ACCESS_0_SPEC>;
#[doc = "Field `CACHE_MMU_ACCESS_LOCK` reader - cache_mmu_access_lock"]
pub type CACHE_MMU_ACCESS_LOCK_R = crate::BitReader;
#[doc = "Field `CACHE_MMU_ACCESS_LOCK` writer - cache_mmu_access_lock"]
pub type CACHE_MMU_ACCESS_LOCK_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - cache_mmu_access_lock"]
    #[inline(always)]
    pub fn cache_mmu_access_lock(&self) -> CACHE_MMU_ACCESS_LOCK_R {
        CACHE_MMU_ACCESS_LOCK_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CACHE_MMU_ACCESS_0")
            .field("cache_mmu_access_lock", &self.cache_mmu_access_lock())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - cache_mmu_access_lock"]
    #[inline(always)]
    pub fn cache_mmu_access_lock(
        &mut self,
    ) -> CACHE_MMU_ACCESS_LOCK_W<'_, CACHE_MMU_ACCESS_0_SPEC> {
        CACHE_MMU_ACCESS_LOCK_W::new(self, 0)
    }
}
#[doc = "SENSITIVE_CACHE_MMU_ACCESS_0_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_mmu_access_0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_mmu_access_0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CACHE_MMU_ACCESS_0_SPEC;
impl crate::RegisterSpec for CACHE_MMU_ACCESS_0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cache_mmu_access_0::R`](R) reader structure"]
impl crate::Readable for CACHE_MMU_ACCESS_0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cache_mmu_access_0::W`](W) writer structure"]
impl crate::Writable for CACHE_MMU_ACCESS_0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CACHE_MMU_ACCESS_0 to value 0"]
impl crate::Resettable for CACHE_MMU_ACCESS_0_SPEC {}
