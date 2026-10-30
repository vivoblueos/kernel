#[doc = "Register `CACHE_SYNC_ADDR` reader"]
pub type R = crate::R<CACHE_SYNC_ADDR_SPEC>;
#[doc = "Register `CACHE_SYNC_ADDR` writer"]
pub type W = crate::W<CACHE_SYNC_ADDR_SPEC>;
#[doc = "Field `CACHE_SYNC_ADDR` reader - Those bits are used to configure the start virtual address of the sync operation, which should be used together with CACHE_SYNC_SIZE_REG"]
pub type CACHE_SYNC_ADDR_R = crate::FieldReader<u32>;
#[doc = "Field `CACHE_SYNC_ADDR` writer - Those bits are used to configure the start virtual address of the sync operation, which should be used together with CACHE_SYNC_SIZE_REG"]
pub type CACHE_SYNC_ADDR_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - Those bits are used to configure the start virtual address of the sync operation, which should be used together with CACHE_SYNC_SIZE_REG"]
    #[inline(always)]
    pub fn cache_sync_addr(&self) -> CACHE_SYNC_ADDR_R {
        CACHE_SYNC_ADDR_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CACHE_SYNC_ADDR")
            .field("cache_sync_addr", &self.cache_sync_addr())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - Those bits are used to configure the start virtual address of the sync operation, which should be used together with CACHE_SYNC_SIZE_REG"]
    #[inline(always)]
    pub fn cache_sync_addr(&mut self) -> CACHE_SYNC_ADDR_W<'_, CACHE_SYNC_ADDR_SPEC> {
        CACHE_SYNC_ADDR_W::new(self, 0)
    }
}
#[doc = "Sync address configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_sync_addr::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_sync_addr::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CACHE_SYNC_ADDR_SPEC;
impl crate::RegisterSpec for CACHE_SYNC_ADDR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cache_sync_addr::R`](R) reader structure"]
impl crate::Readable for CACHE_SYNC_ADDR_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cache_sync_addr::W`](W) writer structure"]
impl crate::Writable for CACHE_SYNC_ADDR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CACHE_SYNC_ADDR to value 0"]
impl crate::Resettable for CACHE_SYNC_ADDR_SPEC {}
