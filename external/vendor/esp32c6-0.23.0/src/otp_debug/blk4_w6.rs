#[doc = "Register `BLK4_W6` reader"]
pub type R = crate::R<BLK4_W6_SPEC>;
#[doc = "Field `BLOCK4_W6` reader - Otp block4 word6 data."]
pub type BLOCK4_W6_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Otp block4 word6 data."]
    #[inline(always)]
    pub fn block4_w6(&self) -> BLOCK4_W6_R {
        BLOCK4_W6_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BLK4_W6")
            .field("block4_w6", &self.block4_w6())
            .finish()
    }
}
#[doc = "Otp debuger block4 data register6.\n\nYou can [`read`](crate::Reg::read) this register and get [`blk4_w6::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BLK4_W6_SPEC;
impl crate::RegisterSpec for BLK4_W6_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`blk4_w6::R`](R) reader structure"]
impl crate::Readable for BLK4_W6_SPEC {}
#[doc = "`reset()` method sets BLK4_W6 to value 0"]
impl crate::Resettable for BLK4_W6_SPEC {}
