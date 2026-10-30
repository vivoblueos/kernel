#[doc = "Register `SLP_WAKEUP_CNTL7` reader"]
pub type R = crate::R<SLP_WAKEUP_CNTL7_SPEC>;
#[doc = "Register `SLP_WAKEUP_CNTL7` writer"]
pub type W = crate::W<SLP_WAKEUP_CNTL7_SPEC>;
#[doc = "Field `ANA_WAIT_TARGET` reader - need_des"]
pub type ANA_WAIT_TARGET_R = crate::FieldReader<u16>;
#[doc = "Field `ANA_WAIT_TARGET` writer - need_des"]
pub type ANA_WAIT_TARGET_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 16:31 - need_des"]
    #[inline(always)]
    pub fn ana_wait_target(&self) -> ANA_WAIT_TARGET_R {
        ANA_WAIT_TARGET_R::new(((self.bits >> 16) & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLP_WAKEUP_CNTL7")
            .field("ana_wait_target", &self.ana_wait_target())
            .finish()
    }
}
impl W {
    #[doc = "Bits 16:31 - need_des"]
    #[inline(always)]
    pub fn ana_wait_target(&mut self) -> ANA_WAIT_TARGET_W<'_, SLP_WAKEUP_CNTL7_SPEC> {
        ANA_WAIT_TARGET_W::new(self, 16)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`slp_wakeup_cntl7::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slp_wakeup_cntl7::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLP_WAKEUP_CNTL7_SPEC;
impl crate::RegisterSpec for SLP_WAKEUP_CNTL7_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slp_wakeup_cntl7::R`](R) reader structure"]
impl crate::Readable for SLP_WAKEUP_CNTL7_SPEC {}
#[doc = "`write(|w| ..)` method takes [`slp_wakeup_cntl7::W`](W) writer structure"]
impl crate::Writable for SLP_WAKEUP_CNTL7_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLP_WAKEUP_CNTL7 to value 0x0001_0000"]
impl crate::Resettable for SLP_WAKEUP_CNTL7_SPEC {
    const RESET_VALUE: u32 = 0x0001_0000;
}
