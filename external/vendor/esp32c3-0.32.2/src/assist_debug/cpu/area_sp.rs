#[doc = "Register `AREA_SP` reader"]
pub type R = crate::R<AREA_SP_SPEC>;
#[doc = "Field `AREA_SP` reader - reg_core_0_area_sp"]
pub type AREA_SP_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - reg_core_0_area_sp"]
    #[inline(always)]
    pub fn area_sp(&self) -> AREA_SP_R {
        AREA_SP_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("AREA_SP")
            .field("area_sp", &self.area_sp())
            .finish()
    }
}
#[doc = "ASSIST_DEBUG_CORE_0_AREA_SP_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`area_sp::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct AREA_SP_SPEC;
impl crate::RegisterSpec for AREA_SP_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`area_sp::R`](R) reader structure"]
impl crate::Readable for AREA_SP_SPEC {}
#[doc = "`reset()` method sets AREA_SP to value 0"]
impl crate::Resettable for AREA_SP_SPEC {}
