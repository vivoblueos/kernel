#[doc = "Register `CACHE_SYNC_SIZE` reader"]
pub type R = crate::R<CACHE_SYNC_SIZE_SPEC>;
#[doc = "Register `CACHE_SYNC_SIZE` writer"]
pub type W = crate::W<CACHE_SYNC_SIZE_SPEC>;
#[doc = "Field `CACHE_SYNC_SIZE` reader - Those bits are used to configure the size of the sync operation, which should be used together with CACHE_SYNC_ADDR_REG"]
pub type CACHE_SYNC_SIZE_R = crate::FieldReader<u32>;
#[doc = "Field `CACHE_SYNC_SIZE` writer - Those bits are used to configure the size of the sync operation, which should be used together with CACHE_SYNC_ADDR_REG"]
pub type CACHE_SYNC_SIZE_W<'a, REG> = crate::FieldWriter<'a, REG, 24, u32>;
impl R {
    #[doc = "Bits 0:23 - Those bits are used to configure the size of the sync operation, which should be used together with CACHE_SYNC_ADDR_REG"]
    #[inline(always)]
    pub fn cache_sync_size(&self) -> CACHE_SYNC_SIZE_R {
        CACHE_SYNC_SIZE_R::new(self.bits & 0x00ff_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CACHE_SYNC_SIZE")
            .field("cache_sync_size", &self.cache_sync_size())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:23 - Those bits are used to configure the size of the sync operation, which should be used together with CACHE_SYNC_ADDR_REG"]
    #[inline(always)]
    pub fn cache_sync_size(&mut self) -> CACHE_SYNC_SIZE_W<'_, CACHE_SYNC_SIZE_SPEC> {
        CACHE_SYNC_SIZE_W::new(self, 0)
    }
}
#[doc = "Sync size configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_sync_size::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_sync_size::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CACHE_SYNC_SIZE_SPEC;
impl crate::RegisterSpec for CACHE_SYNC_SIZE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cache_sync_size::R`](R) reader structure"]
impl crate::Readable for CACHE_SYNC_SIZE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cache_sync_size::W`](W) writer structure"]
impl crate::Writable for CACHE_SYNC_SIZE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CACHE_SYNC_SIZE to value 0"]
impl crate::Resettable for CACHE_SYNC_SIZE_SPEC {}
