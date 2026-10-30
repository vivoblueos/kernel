#[doc = "Register `SLP_WAKEUP_CAUSE` reader"]
pub type R = crate::R<SLP_WAKEUP_CAUSE_SPEC>;
#[doc = "Field `WAKEUP_CAUSE` reader - sleep wakeup cause"]
pub type WAKEUP_CAUSE_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:16 - sleep wakeup cause"]
    #[inline(always)]
    pub fn wakeup_cause(&self) -> WAKEUP_CAUSE_R {
        WAKEUP_CAUSE_R::new(self.bits & 0x0001_ffff)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLP_WAKEUP_CAUSE")
            .field("wakeup_cause", &self.wakeup_cause())
            .finish()
    }
}
#[doc = "RTC_CNTL_RTC_SLP_WAKEUP_CAUSE_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`slp_wakeup_cause::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLP_WAKEUP_CAUSE_SPEC;
impl crate::RegisterSpec for SLP_WAKEUP_CAUSE_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slp_wakeup_cause::R`](R) reader structure"]
impl crate::Readable for SLP_WAKEUP_CAUSE_SPEC {}
#[doc = "`reset()` method sets SLP_WAKEUP_CAUSE to value 0"]
impl crate::Resettable for SLP_WAKEUP_CAUSE_SPEC {}
