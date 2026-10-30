#[doc = "Register `ARB_LOST_CAP` reader"]
pub type R = crate::R<ARB_LOST_CAP_SPEC>;
#[doc = "Field `ARBITRATION_LOST_CAPTURE` reader - This register contains information about the bit position of losing arbitration."]
pub type ARBITRATION_LOST_CAPTURE_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:4 - This register contains information about the bit position of losing arbitration."]
    #[inline(always)]
    pub fn arbitration_lost_capture(&self) -> ARBITRATION_LOST_CAPTURE_R {
        ARBITRATION_LOST_CAPTURE_R::new((self.bits & 0x1f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ARB_LOST_CAP")
            .field("arbitration_lost_capture", &self.arbitration_lost_capture())
            .finish()
    }
}
#[doc = "TWAI arbiter lost capture register.\n\nYou can [`read`](crate::Reg::read) this register and get [`arb_lost_cap::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ARB_LOST_CAP_SPEC;
impl crate::RegisterSpec for ARB_LOST_CAP_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`arb_lost_cap::R`](R) reader structure"]
impl crate::Readable for ARB_LOST_CAP_SPEC {}
#[doc = "`reset()` method sets ARB_LOST_CAP to value 0"]
impl crate::Resettable for ARB_LOST_CAP_SPEC {}
