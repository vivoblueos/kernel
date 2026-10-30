#[doc = "Register `BLK8_W7` reader"]
pub type R = crate::R<BLK8_W7_SPEC>;
#[doc = "Field `BLOCK8_W7` reader - Otp block8 word7 data."]
pub type BLOCK8_W7_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Otp block8 word7 data."]
    #[inline(always)]
    pub fn block8_w7(&self) -> BLOCK8_W7_R {
        BLOCK8_W7_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BLK8_W7")
            .field("block8_w7", &self.block8_w7())
            .finish()
    }
}
#[doc = "Otp debuger block8 data register7.\n\nYou can [`read`](crate::Reg::read) this register and get [`blk8_w7::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BLK8_W7_SPEC;
impl crate::RegisterSpec for BLK8_W7_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`blk8_w7::R`](R) reader structure"]
impl crate::Readable for BLK8_W7_SPEC {}
#[doc = "`reset()` method sets BLK8_W7 to value 0"]
impl crate::Resettable for BLK8_W7_SPEC {}
