#[doc = "Register `SLCHOSTDATE` reader"]
pub type R = crate::R<SLCHOSTDATE_SPEC>;
#[doc = "Register `SLCHOSTDATE` writer"]
pub type W = crate::W<SLCHOSTDATE_SPEC>;
#[doc = "Field `SLCHOST_DATE` reader - *******Description***********"]
pub type SLCHOST_DATE_R = crate::FieldReader<u32>;
#[doc = "Field `SLCHOST_DATE` writer - *******Description***********"]
pub type SLCHOST_DATE_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_date(&self) -> SLCHOST_DATE_R {
        SLCHOST_DATE_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLCHOSTDATE")
            .field("slchost_date", &self.slchost_date())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - *******Description***********"]
    #[inline(always)]
    pub fn slchost_date(&mut self) -> SLCHOST_DATE_W<'_, SLCHOSTDATE_SPEC> {
        SLCHOST_DATE_W::new(self, 0)
    }
}
#[doc = "*******Description***********\n\nYou can [`read`](crate::Reg::read) this register and get [`slchostdate::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slchostdate::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLCHOSTDATE_SPEC;
impl crate::RegisterSpec for SLCHOSTDATE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slchostdate::R`](R) reader structure"]
impl crate::Readable for SLCHOSTDATE_SPEC {}
#[doc = "`write(|w| ..)` method takes [`slchostdate::W`](W) writer structure"]
impl crate::Writable for SLCHOSTDATE_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLCHOSTDATE to value 0x2106_0700"]
impl crate::Resettable for SLCHOSTDATE_SPEC {
    const RESET_VALUE: u32 = 0x2106_0700;
}
