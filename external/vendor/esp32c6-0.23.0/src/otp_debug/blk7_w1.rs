#[doc = "Register `BLK7_W1` reader"]
pub type R = crate::R<BLK7_W1_SPEC>;
#[doc = "Field `BLOCK7_W1` reader - Otp block7 word1 data."]
pub type BLOCK7_W1_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Otp block7 word1 data."]
    #[inline(always)]
    pub fn block7_w1(&self) -> BLOCK7_W1_R {
        BLOCK7_W1_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BLK7_W1")
            .field("block7_w1", &self.block7_w1())
            .finish()
    }
}
#[doc = "Otp debuger block7 data register1.\n\nYou can [`read`](crate::Reg::read) this register and get [`blk7_w1::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BLK7_W1_SPEC;
impl crate::RegisterSpec for BLK7_W1_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`blk7_w1::R`](R) reader structure"]
impl crate::Readable for BLK7_W1_SPEC {}
#[doc = "`reset()` method sets BLK7_W1 to value 0"]
impl crate::Resettable for BLK7_W1_SPEC {}
