#[doc = "Register `BLK10_W4` reader"]
pub type R = crate::R<BLK10_W4_SPEC>;
#[doc = "Field `BLOCK10_W4` reader - Otp block10 word4 data."]
pub type BLOCK10_W4_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Otp block10 word4 data."]
    #[inline(always)]
    pub fn block10_w4(&self) -> BLOCK10_W4_R {
        BLOCK10_W4_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BLK10_W4")
            .field("block10_w4", &self.block10_w4())
            .finish()
    }
}
#[doc = "Otp debuger block10 data register4.\n\nYou can [`read`](crate::Reg::read) this register and get [`blk10_w4::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BLK10_W4_SPEC;
impl crate::RegisterSpec for BLK10_W4_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`blk10_w4::R`](R) reader structure"]
impl crate::Readable for BLK10_W4_SPEC {}
#[doc = "`reset()` method sets BLK10_W4 to value 0"]
impl crate::Resettable for BLK10_W4_SPEC {}
