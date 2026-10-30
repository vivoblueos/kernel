#[doc = "Register `RCD_PDEBUGSP` reader"]
pub type R = crate::R<RCD_PDEBUGSP_SPEC>;
#[doc = "Field `RCD_PDEBUGSP` reader - recorded sp"]
pub type RCD_PDEBUGSP_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - recorded sp"]
    #[inline(always)]
    pub fn rcd_pdebugsp(&self) -> RCD_PDEBUGSP_R {
        RCD_PDEBUGSP_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RCD_PDEBUGSP")
            .field("rcd_pdebugsp", &self.rcd_pdebugsp())
            .finish()
    }
}
#[doc = "record status regsiter\n\nYou can [`read`](crate::Reg::read) this register and get [`rcd_pdebugsp::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RCD_PDEBUGSP_SPEC;
impl crate::RegisterSpec for RCD_PDEBUGSP_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rcd_pdebugsp::R`](R) reader structure"]
impl crate::Readable for RCD_PDEBUGSP_SPEC {}
#[doc = "`reset()` method sets RCD_PDEBUGSP to value 0"]
impl crate::Resettable for RCD_PDEBUGSP_SPEC {}
