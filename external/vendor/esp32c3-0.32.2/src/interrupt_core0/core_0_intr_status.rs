#[doc = "Register `CORE_0_INTR_STATUS%s` reader"]
pub type R = crate::R<CORE_0_INTR_STATUS_SPEC>;
#[doc = "Field `INTR_STATUS_0` reader - reg_core0_intr_status_0"]
pub type INTR_STATUS_0_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - reg_core0_intr_status_0"]
    #[inline(always)]
    pub fn intr_status_0(&self) -> INTR_STATUS_0_R {
        INTR_STATUS_0_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CORE_0_INTR_STATUS")
            .field("intr_status_0", &self.intr_status_0())
            .finish()
    }
}
#[doc = "mac intr map register\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_intr_status::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CORE_0_INTR_STATUS_SPEC;
impl crate::RegisterSpec for CORE_0_INTR_STATUS_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`core_0_intr_status::R`](R) reader structure"]
impl crate::Readable for CORE_0_INTR_STATUS_SPEC {}
#[doc = "`reset()` method sets CORE_0_INTR_STATUS%s to value 0"]
impl crate::Resettable for CORE_0_INTR_STATUS_SPEC {}
