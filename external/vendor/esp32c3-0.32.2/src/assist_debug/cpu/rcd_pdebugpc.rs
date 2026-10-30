#[doc = "Register `RCD_PDEBUGPC` reader"]
pub type R = crate::R<RCD_PDEBUGPC_SPEC>;
#[doc = "Field `RCD_PDEBUGPC` reader - reg_core_0_rcd_pdebugpc"]
pub type RCD_PDEBUGPC_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - reg_core_0_rcd_pdebugpc"]
    #[inline(always)]
    pub fn rcd_pdebugpc(&self) -> RCD_PDEBUGPC_R {
        RCD_PDEBUGPC_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RCD_PDEBUGPC")
            .field("rcd_pdebugpc", &self.rcd_pdebugpc())
            .finish()
    }
}
#[doc = "ASSIST_DEBUG_CORE_0_RCD_PDEBUGPC_REG\n\nYou can [`read`](crate::Reg::read) this register and get [`rcd_pdebugpc::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RCD_PDEBUGPC_SPEC;
impl crate::RegisterSpec for RCD_PDEBUGPC_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rcd_pdebugpc::R`](R) reader structure"]
impl crate::Readable for RCD_PDEBUGPC_SPEC {}
#[doc = "`reset()` method sets RCD_PDEBUGPC to value 0"]
impl crate::Resettable for RCD_PDEBUGPC_SPEC {}
