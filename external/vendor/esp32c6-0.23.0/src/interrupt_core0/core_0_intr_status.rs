#[doc = "Register `CORE_0_INTR_STATUS%s` reader"]
pub type R = crate::R<CORE_0_INTR_STATUS_SPEC>;
#[doc = "Field `INT_STATUS_0` reader - Need add description"]
pub type INT_STATUS_0_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Need add description"]
    #[inline(always)]
    pub fn int_status_0(&self) -> INT_STATUS_0_R {
        INT_STATUS_0_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CORE_0_INTR_STATUS")
            .field("int_status_0", &self.int_status_0())
            .finish()
    }
}
#[doc = "register description\n\nYou can [`read`](crate::Reg::read) this register and get [`core_0_intr_status::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CORE_0_INTR_STATUS_SPEC;
impl crate::RegisterSpec for CORE_0_INTR_STATUS_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`core_0_intr_status::R`](R) reader structure"]
impl crate::Readable for CORE_0_INTR_STATUS_SPEC {}
#[doc = "`reset()` method sets CORE_0_INTR_STATUS%s to value 0"]
impl crate::Resettable for CORE_0_INTR_STATUS_SPEC {}
