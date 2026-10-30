#[doc = "Register `DIAG0` reader"]
pub type R = crate::R<DIAG0_SPEC>;
#[doc = "Field `LOW_POWER_DIAG1` reader - "]
pub type LOW_POWER_DIAG1_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31"]
    #[inline(always)]
    pub fn low_power_diag1(&self) -> LOW_POWER_DIAG1_R {
        LOW_POWER_DIAG1_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("DIAG0")
            .field("low_power_diag1", &self.low_power_diag1())
            .finish()
    }
}
#[doc = "rtc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`diag0::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DIAG0_SPEC;
impl crate::RegisterSpec for DIAG0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`diag0::R`](R) reader structure"]
impl crate::Readable for DIAG0_SPEC {}
#[doc = "`reset()` method sets DIAG0 to value 0"]
impl crate::Resettable for DIAG0_SPEC {}
