#[doc = "Register `BLK2_W1` reader"]
pub type R = crate::R<BLK2_W1_SPEC>;
#[doc = "Field `BLOCK2_W1` reader - Otp block2 word1 data."]
pub type BLOCK2_W1_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Otp block2 word1 data."]
    #[inline(always)]
    pub fn block2_w1(&self) -> BLOCK2_W1_R {
        BLOCK2_W1_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BLK2_W1")
            .field("block2_w1", &self.block2_w1())
            .finish()
    }
}
#[doc = "Otp debuger block2 data register1.\n\nYou can [`read`](crate::Reg::read) this register and get [`blk2_w1::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BLK2_W1_SPEC;
impl crate::RegisterSpec for BLK2_W1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`blk2_w1::R`](R) reader structure"]
impl crate::Readable for BLK2_W1_SPEC {}
#[doc = "`reset()` method sets BLK2_W1 to value 0"]
impl crate::Resettable for BLK2_W1_SPEC {}
