#[doc = "Register `CACHE_SYNC_MAP` reader"]
pub type R = crate::R<CACHE_SYNC_MAP_SPEC>;
#[doc = "Register `CACHE_SYNC_MAP` writer"]
pub type W = crate::W<CACHE_SYNC_MAP_SPEC>;
#[doc = "Field `CACHE_SYNC_MAP` reader - Those bits are used to indicate which caches in the two-level cache structure will apply the sync operation. \\[4\\]: L1-Cache"]
pub type CACHE_SYNC_MAP_R = crate::FieldReader;
#[doc = "Field `CACHE_SYNC_MAP` writer - Those bits are used to indicate which caches in the two-level cache structure will apply the sync operation. \\[4\\]: L1-Cache"]
pub type CACHE_SYNC_MAP_W<'a, REG> = crate::FieldWriter<'a, REG, 6>;
impl R {
    #[doc = "Bits 0:5 - Those bits are used to indicate which caches in the two-level cache structure will apply the sync operation. \\[4\\]: L1-Cache"]
    #[inline(always)]
    pub fn cache_sync_map(&self) -> CACHE_SYNC_MAP_R {
        CACHE_SYNC_MAP_R::new((self.bits & 0x3f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CACHE_SYNC_MAP")
            .field("cache_sync_map", &self.cache_sync_map())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:5 - Those bits are used to indicate which caches in the two-level cache structure will apply the sync operation. \\[4\\]: L1-Cache"]
    #[inline(always)]
    pub fn cache_sync_map(&mut self) -> CACHE_SYNC_MAP_W<'_, CACHE_SYNC_MAP_SPEC> {
        CACHE_SYNC_MAP_W::new(self, 0)
    }
}
#[doc = "Sync map configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_sync_map::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_sync_map::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CACHE_SYNC_MAP_SPEC;
impl crate::RegisterSpec for CACHE_SYNC_MAP_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cache_sync_map::R`](R) reader structure"]
impl crate::Readable for CACHE_SYNC_MAP_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cache_sync_map::W`](W) writer structure"]
impl crate::Writable for CACHE_SYNC_MAP_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CACHE_SYNC_MAP to value 0x3f"]
impl crate::Resettable for CACHE_SYNC_MAP_SPEC {
    const RESET_VALUE: u32 = 0x3f;
}
