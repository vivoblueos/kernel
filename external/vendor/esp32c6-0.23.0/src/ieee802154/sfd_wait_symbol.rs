#[doc = "Register `SFD_WAIT_SYMBOL` reader"]
pub type R = crate::R<SFD_WAIT_SYMBOL_SPEC>;
#[doc = "Register `SFD_WAIT_SYMBOL` writer"]
pub type W = crate::W<SFD_WAIT_SYMBOL_SPEC>;
#[doc = "Field `NUM` reader - "]
pub type NUM_R = crate::FieldReader;
#[doc = "Field `NUM` writer - "]
pub type NUM_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bits 0:3"]
    #[inline(always)]
    pub fn num(&self) -> NUM_R {
        NUM_R::new((self.bits & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SFD_WAIT_SYMBOL")
            .field("num", &self.num())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:3"]
    #[inline(always)]
    pub fn num(&mut self) -> NUM_W<'_, SFD_WAIT_SYMBOL_SPEC> {
        NUM_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`sfd_wait_symbol::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sfd_wait_symbol::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SFD_WAIT_SYMBOL_SPEC;
impl crate::RegisterSpec for SFD_WAIT_SYMBOL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sfd_wait_symbol::R`](R) reader structure"]
impl crate::Readable for SFD_WAIT_SYMBOL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`sfd_wait_symbol::W`](W) writer structure"]
impl crate::Writable for SFD_WAIT_SYMBOL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SFD_WAIT_SYMBOL to value 0"]
impl crate::Resettable for SFD_WAIT_SYMBOL_SPEC {}
