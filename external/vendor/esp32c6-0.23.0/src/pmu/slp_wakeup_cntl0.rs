#[doc = "Register `SLP_WAKEUP_CNTL0` writer"]
pub type W = crate::W<SLP_WAKEUP_CNTL0_SPEC>;
#[doc = "Field `SLEEP_REQ` writer - need_des"]
pub type SLEEP_REQ_W<'a, REG> = crate::BitWriter<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<SLP_WAKEUP_CNTL0_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn sleep_req(&mut self) -> SLEEP_REQ_W<'_, SLP_WAKEUP_CNTL0_SPEC> {
        SLEEP_REQ_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slp_wakeup_cntl0::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLP_WAKEUP_CNTL0_SPEC;
impl crate::RegisterSpec for SLP_WAKEUP_CNTL0_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`slp_wakeup_cntl0::W`](W) writer structure"]
impl crate::Writable for SLP_WAKEUP_CNTL0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLP_WAKEUP_CNTL0 to value 0"]
impl crate::Resettable for SLP_WAKEUP_CNTL0_SPEC {}
