#[doc = "Register `SLP_WAKEUP_STATUS0` reader"]
pub type R = crate::R<SLP_WAKEUP_STATUS0_SPEC>;
#[doc = "Field `WAKEUP_CAUSE` reader - need_des"]
pub type WAKEUP_CAUSE_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - need_des"]
    #[inline(always)]
    pub fn wakeup_cause(&self) -> WAKEUP_CAUSE_R {
        WAKEUP_CAUSE_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLP_WAKEUP_STATUS0")
            .field("wakeup_cause", &self.wakeup_cause())
            .finish()
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`slp_wakeup_status0::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLP_WAKEUP_STATUS0_SPEC;
impl crate::RegisterSpec for SLP_WAKEUP_STATUS0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slp_wakeup_status0::R`](R) reader structure"]
impl crate::Readable for SLP_WAKEUP_STATUS0_SPEC {}
#[doc = "`reset()` method sets SLP_WAKEUP_STATUS0 to value 0"]
impl crate::Resettable for SLP_WAKEUP_STATUS0_SPEC {}
