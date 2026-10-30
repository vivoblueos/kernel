#[doc = "Register `CACHE_REQUEST` reader"]
pub type R = crate::R<CACHE_REQUEST_SPEC>;
#[doc = "Register `CACHE_REQUEST` writer"]
pub type W = crate::W<CACHE_REQUEST_SPEC>;
#[doc = "Field `BYPASS` reader - The bit is used to disable request recording which could cause performance issue"]
pub type BYPASS_R = crate::BitReader;
#[doc = "Field `BYPASS` writer - The bit is used to disable request recording which could cause performance issue"]
pub type BYPASS_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - The bit is used to disable request recording which could cause performance issue"]
    #[inline(always)]
    pub fn bypass(&self) -> BYPASS_R {
        BYPASS_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CACHE_REQUEST")
            .field("bypass", &self.bypass())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - The bit is used to disable request recording which could cause performance issue"]
    #[inline(always)]
    pub fn bypass(&mut self) -> BYPASS_W<'_, CACHE_REQUEST_SPEC> {
        BYPASS_W::new(self, 0)
    }
}
#[doc = "This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_request::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_request::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CACHE_REQUEST_SPEC;
impl crate::RegisterSpec for CACHE_REQUEST_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cache_request::R`](R) reader structure"]
impl crate::Readable for CACHE_REQUEST_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cache_request::W`](W) writer structure"]
impl crate::Writable for CACHE_REQUEST_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CACHE_REQUEST to value 0"]
impl crate::Resettable for CACHE_REQUEST_SPEC {}
