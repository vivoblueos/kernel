#[doc = "Register `BLK5_W5` reader"]
pub type R = crate::R<BLK5_W5_SPEC>;
#[doc = "Field `BLOCK5_W5` reader - Otp block5 word5 data."]
pub type BLOCK5_W5_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Otp block5 word5 data."]
    #[inline(always)]
    pub fn block5_w5(&self) -> BLOCK5_W5_R {
        BLOCK5_W5_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BLK5_W5")
            .field("block5_w5", &self.block5_w5())
            .finish()
    }
}
#[doc = "Otp debuger block5 data register5.\n\nYou can [`read`](crate::Reg::read) this register and get [`blk5_w5::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BLK5_W5_SPEC;
impl crate::RegisterSpec for BLK5_W5_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`blk5_w5::R`](R) reader structure"]
impl crate::Readable for BLK5_W5_SPEC {}
#[doc = "`reset()` method sets BLK5_W5 to value 0"]
impl crate::Resettable for BLK5_W5_SPEC {}
