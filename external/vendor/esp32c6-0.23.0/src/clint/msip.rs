#[doc = "Register `MSIP` reader"]
pub type R = crate::R<MSIP_SPEC>;
#[doc = "Register `MSIP` writer"]
pub type W = crate::W<MSIP_SPEC>;
#[doc = "Field `MSIP` reader - Configures the pending status of the machine software interrupt."]
pub type MSIP_R = crate::BitReader;
#[doc = "Field `MSIP` writer - Configures the pending status of the machine software interrupt."]
pub type MSIP_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Configures the pending status of the machine software interrupt."]
    #[inline(always)]
    pub fn msip(&self) -> MSIP_R {
        MSIP_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("MSIP").field("msip", &self.msip()).finish()
    }
}
impl W {
    #[doc = "Bit 0 - Configures the pending status of the machine software interrupt."]
    #[inline(always)]
    pub fn msip(&mut self) -> MSIP_W<'_, MSIP_SPEC> {
        MSIP_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`msip::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`msip::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MSIP_SPEC;
impl crate::RegisterSpec for MSIP_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`msip::R`](R) reader structure"]
impl crate::Readable for MSIP_SPEC {}
#[doc = "`write(|w| ..)` method takes [`msip::W`](W) writer structure"]
impl crate::Writable for MSIP_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets MSIP to value 0"]
impl crate::Resettable for MSIP_SPEC {}
