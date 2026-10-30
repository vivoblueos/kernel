#[doc = "Register `SLP_WAKEUP_CNTL2` reader"]
pub type R = crate::R<SLP_WAKEUP_CNTL2_SPEC>;
#[doc = "Register `SLP_WAKEUP_CNTL2` writer"]
pub type W = crate::W<SLP_WAKEUP_CNTL2_SPEC>;
#[doc = "Field `WAKEUP_ENA` reader - need_des"]
pub type WAKEUP_ENA_R = crate::FieldReader<u32>;
#[doc = "Field `WAKEUP_ENA` writer - need_des"]
pub type WAKEUP_ENA_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - need_des"]
    #[inline(always)]
    pub fn wakeup_ena(&self) -> WAKEUP_ENA_R {
        WAKEUP_ENA_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLP_WAKEUP_CNTL2")
            .field("wakeup_ena", &self.wakeup_ena())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31 - need_des"]
    #[inline(always)]
    pub fn wakeup_ena(&mut self) -> WAKEUP_ENA_W<'_, SLP_WAKEUP_CNTL2_SPEC> {
        WAKEUP_ENA_W::new(self, 0)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`slp_wakeup_cntl2::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slp_wakeup_cntl2::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLP_WAKEUP_CNTL2_SPEC;
impl crate::RegisterSpec for SLP_WAKEUP_CNTL2_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slp_wakeup_cntl2::R`](R) reader structure"]
impl crate::Readable for SLP_WAKEUP_CNTL2_SPEC {}
#[doc = "`write(|w| ..)` method takes [`slp_wakeup_cntl2::W`](W) writer structure"]
impl crate::Writable for SLP_WAKEUP_CNTL2_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLP_WAKEUP_CNTL2 to value 0"]
impl crate::Resettable for SLP_WAKEUP_CNTL2_SPEC {}
