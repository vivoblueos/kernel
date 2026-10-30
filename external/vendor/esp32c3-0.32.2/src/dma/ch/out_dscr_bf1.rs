#[doc = "Register `OUT_DSCR_BF1` reader"]
pub type R = crate::R<OUT_DSCR_BF1_SPEC>;
#[doc = "Field `OUTLINK_DSCR_BF1` reader - The address of the second-to-last inlink descriptor x-2."]
pub type OUTLINK_DSCR_BF1_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - The address of the second-to-last inlink descriptor x-2."]
    #[inline(always)]
    pub fn outlink_dscr_bf1(&self) -> OUTLINK_DSCR_BF1_R {
        OUTLINK_DSCR_BF1_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("OUT_DSCR_BF1")
            .field("outlink_dscr_bf1", &self.outlink_dscr_bf1())
            .finish()
    }
}
#[doc = "DMA_OUT_DSCR_BF1_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`out_dscr_bf1::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct OUT_DSCR_BF1_SPEC;
impl crate::RegisterSpec for OUT_DSCR_BF1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`out_dscr_bf1::R`](R) reader structure"]
impl crate::Readable for OUT_DSCR_BF1_SPEC {}
#[doc = "`reset()` method sets OUT_DSCR_BF1 to value 0"]
impl crate::Resettable for OUT_DSCR_BF1_SPEC {}
