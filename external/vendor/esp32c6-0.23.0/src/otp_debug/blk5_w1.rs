#[doc = "Register `BLK5_W1` reader"]
pub type R = crate::R<BLK5_W1_SPEC>;
#[doc = "Field `BLOCK5_W1` reader - Otp block5 word1 data."]
pub type BLOCK5_W1_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Otp block5 word1 data."]
    #[inline(always)]
    pub fn block5_w1(&self) -> BLOCK5_W1_R {
        BLOCK5_W1_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BLK5_W1")
            .field("block5_w1", &self.block5_w1())
            .finish()
    }
}
#[doc = "Otp debuger block5 data register1.\n\nYou can [`read`](crate::Reg::read) this register and get [`blk5_w1::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BLK5_W1_SPEC;
impl crate::RegisterSpec for BLK5_W1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`blk5_w1::R`](R) reader structure"]
impl crate::Readable for BLK5_W1_SPEC {}
#[doc = "`reset()` method sets BLK5_W1 to value 0"]
impl crate::Resettable for BLK5_W1_SPEC {}
