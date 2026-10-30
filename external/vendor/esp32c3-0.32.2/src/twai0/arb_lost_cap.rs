#[doc = "Register `ARB_LOST_CAP` reader"]
pub type R = crate::R<ARB_LOST_CAP_SPEC>;
#[doc = "Field `ARB_LOST_CAP` reader - This register contains information about the bit position of lost arbitration."]
pub type ARB_LOST_CAP_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:4 - This register contains information about the bit position of lost arbitration."]
    #[inline(always)]
    pub fn arb_lost_cap(&self) -> ARB_LOST_CAP_R {
        ARB_LOST_CAP_R::new((self.bits & 0x1f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ARB_LOST_CAP")
            .field("arb_lost_cap", &self.arb_lost_cap())
            .finish()
    }
}
#[doc = "Arbitration Lost Capture Register\n\nYou can [`read`](crate::Reg::read) this register and get [`arb_lost_cap::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ARB_LOST_CAP_SPEC;
impl crate::RegisterSpec for ARB_LOST_CAP_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`arb_lost_cap::R`](R) reader structure"]
impl crate::Readable for ARB_LOST_CAP_SPEC {}
#[doc = "`reset()` method sets ARB_LOST_CAP to value 0"]
impl crate::Resettable for ARB_LOST_CAP_SPEC {}
