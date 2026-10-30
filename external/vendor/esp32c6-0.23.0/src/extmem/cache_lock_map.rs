#[doc = "Register `CACHE_LOCK_MAP` reader"]
pub type R = crate::R<CACHE_LOCK_MAP_SPEC>;
#[doc = "Register `CACHE_LOCK_MAP` writer"]
pub type W = crate::W<CACHE_LOCK_MAP_SPEC>;
#[doc = "Field `CACHE_LOCK_MAP` reader - Those bits are used to indicate which caches in the two-level cache structure will apply this lock/unlock operation. \\[4\\]: L1-Cache"]
pub type CACHE_LOCK_MAP_R = crate::FieldReader;
#[doc = "Field `CACHE_LOCK_MAP` writer - Those bits are used to indicate which caches in the two-level cache structure will apply this lock/unlock operation. \\[4\\]: L1-Cache"]
pub type CACHE_LOCK_MAP_W<'a, REG> = crate::FieldWriter<'a, REG, 6>;
impl R {
    #[doc = "Bits 0:5 - Those bits are used to indicate which caches in the two-level cache structure will apply this lock/unlock operation. \\[4\\]: L1-Cache"]
    #[inline(always)]
    pub fn cache_lock_map(&self) -> CACHE_LOCK_MAP_R {
        CACHE_LOCK_MAP_R::new((self.bits & 0x3f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CACHE_LOCK_MAP")
            .field("cache_lock_map", &self.cache_lock_map())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:5 - Those bits are used to indicate which caches in the two-level cache structure will apply this lock/unlock operation. \\[4\\]: L1-Cache"]
    #[inline(always)]
    pub fn cache_lock_map(&mut self) -> CACHE_LOCK_MAP_W<'_, CACHE_LOCK_MAP_SPEC> {
        CACHE_LOCK_MAP_W::new(self, 0)
    }
}
#[doc = "Lock (manual lock) map configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_lock_map::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_lock_map::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CACHE_LOCK_MAP_SPEC;
impl crate::RegisterSpec for CACHE_LOCK_MAP_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cache_lock_map::R`](R) reader structure"]
impl crate::Readable for CACHE_LOCK_MAP_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cache_lock_map::W`](W) writer structure"]
impl crate::Writable for CACHE_LOCK_MAP_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CACHE_LOCK_MAP to value 0"]
impl crate::Resettable for CACHE_LOCK_MAP_SPEC {}
