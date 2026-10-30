#[doc = "Register `IN_DSCR` reader"]
pub type R = crate::R<IN_DSCR_SPEC>;
#[doc = "Field `INLINK_DSCR` reader - The address of the current inlink descriptor x."]
pub type INLINK_DSCR_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - The address of the current inlink descriptor x."]
    #[inline(always)]
    pub fn inlink_dscr(&self) -> INLINK_DSCR_R {
        INLINK_DSCR_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("IN_DSCR")
            .field("inlink_dscr", &self.inlink_dscr())
            .finish()
    }
}
#[doc = "Current inlink descriptor address of Rx channel 0\n\nYou can [`read`](crate::Reg::read) this register and get [`in_dscr::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IN_DSCR_SPEC;
impl crate::RegisterSpec for IN_DSCR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`in_dscr::R`](R) reader structure"]
impl crate::Readable for IN_DSCR_SPEC {}
#[doc = "`reset()` method sets IN_DSCR to value 0"]
impl crate::Resettable for IN_DSCR_SPEC {}
