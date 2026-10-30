#[doc = "Register `SLP_WAKEUP_CNTL4` writer"]
pub type W = crate::W<SLP_WAKEUP_CNTL4_SPEC>;
#[doc = "Field `SLP_REJECT_CAUSE_CLR` writer - need_des"]
pub type SLP_REJECT_CAUSE_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<SLP_WAKEUP_CNTL4_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn slp_reject_cause_clr(&mut self) -> SLP_REJECT_CAUSE_CLR_W<'_, SLP_WAKEUP_CNTL4_SPEC> {
        SLP_REJECT_CAUSE_CLR_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slp_wakeup_cntl4::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLP_WAKEUP_CNTL4_SPEC;
impl crate::RegisterSpec for SLP_WAKEUP_CNTL4_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`slp_wakeup_cntl4::W`](W) writer structure"]
impl crate::Writable for SLP_WAKEUP_CNTL4_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLP_WAKEUP_CNTL4 to value 0"]
impl crate::Resettable for SLP_WAKEUP_CNTL4_SPEC {}
