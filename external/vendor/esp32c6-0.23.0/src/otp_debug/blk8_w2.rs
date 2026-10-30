#[doc = "Register `BLK8_W2` reader"]
pub type R = crate::R<BLK8_W2_SPEC>;
#[doc = "Field `BLOCK8_W2` reader - Otp block8 word2 data."]
pub type BLOCK8_W2_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Otp block8 word2 data."]
    #[inline(always)]
    pub fn block8_w2(&self) -> BLOCK8_W2_R {
        BLOCK8_W2_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BLK8_W2")
            .field("block8_w2", &self.block8_w2())
            .finish()
    }
}
#[doc = "Otp debuger block8 data register2.\n\nYou can [`read`](crate::Reg::read) this register and get [`blk8_w2::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BLK8_W2_SPEC;
impl crate::RegisterSpec for BLK8_W2_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`blk8_w2::R`](R) reader structure"]
impl crate::Readable for BLK8_W2_SPEC {}
#[doc = "`reset()` method sets BLK8_W2 to value 0"]
impl crate::Resettable for BLK8_W2_SPEC {}
