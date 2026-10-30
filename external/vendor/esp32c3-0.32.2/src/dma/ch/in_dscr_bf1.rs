#[doc = "Register `IN_DSCR_BF1` reader"]
pub type R = crate::R<IN_DSCR_BF1_SPEC>;
#[doc = "Field `INLINK_DSCR_BF1` reader - The address of the second-to-last inlink descriptor x-2."]
pub type INLINK_DSCR_BF1_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - The address of the second-to-last inlink descriptor x-2."]
    #[inline(always)]
    pub fn inlink_dscr_bf1(&self) -> INLINK_DSCR_BF1_R {
        INLINK_DSCR_BF1_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("IN_DSCR_BF1")
            .field("inlink_dscr_bf1", &self.inlink_dscr_bf1())
            .finish()
    }
}
#[doc = "DMA_IN_DSCR_BF1_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`in_dscr_bf1::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IN_DSCR_BF1_SPEC;
impl crate::RegisterSpec for IN_DSCR_BF1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`in_dscr_bf1::R`](R) reader structure"]
impl crate::Readable for IN_DSCR_BF1_SPEC {}
#[doc = "`reset()` method sets IN_DSCR_BF1 to value 0"]
impl crate::Resettable for IN_DSCR_BF1_SPEC {}
