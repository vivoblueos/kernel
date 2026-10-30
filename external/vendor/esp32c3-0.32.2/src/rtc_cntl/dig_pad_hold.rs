#[doc = "Register `DIG_PAD_HOLD` reader"]
pub type R = crate::R<DIG_PAD_HOLD_SPEC>;
#[doc = "Register `DIG_PAD_HOLD` writer"]
pub type W = crate::W<DIG_PAD_HOLD_SPEC>;
#[doc = "Field `DIG_PAD_HOLD` reader - the configure of digital pad"]
pub type DIG_PAD_HOLD_R = crate::FieldReader<u32>;
#[doc = "Field `DIG_PAD_HOLD` writer - the configure of digital pad"]
pub type DIG_PAD_HOLD_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - the configure of digital pad"]
    #[inline(always)]
    pub fn dig_pad_hold(&self) -> DIG_PAD_HOLD_R {
        DIG_PAD_HOLD_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("DIG_PAD_HOLD")
            .field("dig_pad_hold", &self.dig_pad_hold())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - the configure of digital pad"]
    #[inline(always)]
    pub fn dig_pad_hold(&mut self) -> DIG_PAD_HOLD_W<'_, DIG_PAD_HOLD_SPEC> {
        DIG_PAD_HOLD_W::new(self, 0)
    }
}
#[doc = "rtc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`dig_pad_hold::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dig_pad_hold::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DIG_PAD_HOLD_SPEC;
impl crate::RegisterSpec for DIG_PAD_HOLD_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dig_pad_hold::R`](R) reader structure"]
impl crate::Readable for DIG_PAD_HOLD_SPEC {}
#[doc = "`write(|w| ..)` method takes [`dig_pad_hold::W`](W) writer structure"]
impl crate::Writable for DIG_PAD_HOLD_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets DIG_PAD_HOLD to value 0"]
impl crate::Resettable for DIG_PAD_HOLD_SPEC {}
