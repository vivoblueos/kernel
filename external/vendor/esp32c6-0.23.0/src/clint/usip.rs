#[doc = "Register `USIP` reader"]
pub type R = crate::R<USIP_SPEC>;
#[doc = "Register `USIP` writer"]
pub type W = crate::W<USIP_SPEC>;
#[doc = "Field `USIP` reader - Configures the pending status of the user software interrupt."]
pub type USIP_R = crate::BitReader;
#[doc = "Field `USIP` writer - Configures the pending status of the user software interrupt."]
pub type USIP_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Configures the pending status of the user software interrupt."]
    #[inline(always)]
    pub fn usip(&self) -> USIP_R {
        USIP_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("USIP").field("usip", &self.usip()).finish()
    }
}
impl W {
    #[doc = "Bit 0 - Configures the pending status of the user software interrupt."]
    #[inline(always)]
    pub fn usip(&mut self) -> USIP_W<'_, USIP_SPEC> {
        USIP_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`usip::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`usip::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct USIP_SPEC;
impl crate::RegisterSpec for USIP_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`usip::R`](R) reader structure"]
impl crate::Readable for USIP_SPEC {}
#[doc = "`write(|w| ..)` method takes [`usip::W`](W) writer structure"]
impl crate::Writable for USIP_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets USIP to value 0"]
impl crate::Resettable for USIP_SPEC {}
