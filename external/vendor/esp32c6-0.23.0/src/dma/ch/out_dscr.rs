#[doc = "Register `OUT_DSCR` reader"]
pub type R = crate::R<OUT_DSCR_SPEC>;
#[doc = "Field `OUTLINK_DSCR` reader - The address of the current outlink descriptor y."]
pub type OUTLINK_DSCR_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - The address of the current outlink descriptor y."]
    #[inline(always)]
    pub fn outlink_dscr(&self) -> OUTLINK_DSCR_R {
        OUTLINK_DSCR_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("OUT_DSCR")
            .field("outlink_dscr", &self.outlink_dscr())
            .finish()
    }
}
#[doc = "Current inlink descriptor address of Tx channel 0\n\nYou can [`read`](crate::Reg::read) this register and get [`out_dscr::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct OUT_DSCR_SPEC;
impl crate::RegisterSpec for OUT_DSCR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`out_dscr::R`](R) reader structure"]
impl crate::Readable for OUT_DSCR_SPEC {}
#[doc = "`reset()` method sets OUT_DSCR to value 0"]
impl crate::Resettable for OUT_DSCR_SPEC {}
