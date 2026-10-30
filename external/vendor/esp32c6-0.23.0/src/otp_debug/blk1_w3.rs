#[doc = "Register `BLK1_W3` reader"]
pub type R = crate::R<BLK1_W3_SPEC>;
#[doc = "Field `BLOCK1_W3` reader - Otp block1 word3 data."]
pub type BLOCK1_W3_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Otp block1 word3 data."]
    #[inline(always)]
    pub fn block1_w3(&self) -> BLOCK1_W3_R {
        BLOCK1_W3_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BLK1_W3")
            .field("block1_w3", &self.block1_w3())
            .finish()
    }
}
#[doc = "Otp debuger block1 data register3.\n\nYou can [`read`](crate::Reg::read) this register and get [`blk1_w3::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BLK1_W3_SPEC;
impl crate::RegisterSpec for BLK1_W3_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`blk1_w3::R`](R) reader structure"]
impl crate::Readable for BLK1_W3_SPEC {}
#[doc = "`reset()` method sets BLK1_W3 to value 0"]
impl crate::Resettable for BLK1_W3_SPEC {}
