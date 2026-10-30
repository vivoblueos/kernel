#[doc = "Register `RELEASE` writer"]
pub type W = crate::W<RELEASE_SPEC>;
#[doc = "Field `RELEASE` writer - Set this bit to release the manual encrypted result, after that the result will be visible to spi"]
pub type RELEASE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<RELEASE_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - Set this bit to release the manual encrypted result, after that the result will be visible to spi"]
    #[inline(always)]
    pub fn release(&mut self) -> RELEASE_W<'_, RELEASE_SPEC> {
        RELEASE_W::new(self, 0)
    }
}
#[doc = "XTS-AES release register\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`release::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RELEASE_SPEC;
impl crate::RegisterSpec for RELEASE_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`release::W`](W) writer structure"]
impl crate::Writable for RELEASE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets RELEASE to value 0"]
impl crate::Resettable for RELEASE_SPEC {}
