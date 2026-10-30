#[doc = "Register `DESTROY` writer"]
pub type W = crate::W<DESTROY_SPEC>;
#[doc = "Field `DESTROY` writer - Set this bit to destroy XTS-AES result."]
pub type DESTROY_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<DESTROY_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - Set this bit to destroy XTS-AES result."]
    #[inline(always)]
    pub fn destroy(&mut self) -> DESTROY_W<'_, DESTROY_SPEC> {
        DESTROY_W::new(self, 0)
    }
}
#[doc = "XTS-AES destroy register\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`destroy::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DESTROY_SPEC;
impl crate::RegisterSpec for DESTROY_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`destroy::W`](W) writer structure"]
impl crate::Writable for DESTROY_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets DESTROY to value 0"]
impl crate::Resettable for DESTROY_SPEC {}
