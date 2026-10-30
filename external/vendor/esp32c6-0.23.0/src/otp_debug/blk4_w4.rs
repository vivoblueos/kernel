#[doc = "Register `BLK4_W4` reader"]
pub type R = crate::R<BLK4_W4_SPEC>;
#[doc = "Field `BLOCK4_W4` reader - Otp block4 word4 data."]
pub type BLOCK4_W4_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Otp block4 word4 data."]
    #[inline(always)]
    pub fn block4_w4(&self) -> BLOCK4_W4_R {
        BLOCK4_W4_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BLK4_W4")
            .field("block4_w4", &self.block4_w4())
            .finish()
    }
}
#[doc = "Otp debuger block4 data register4.\n\nYou can [`read`](crate::Reg::read) this register and get [`blk4_w4::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BLK4_W4_SPEC;
impl crate::RegisterSpec for BLK4_W4_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`blk4_w4::R`](R) reader structure"]
impl crate::Readable for BLK4_W4_SPEC {}
#[doc = "`reset()` method sets BLK4_W4 to value 0"]
impl crate::Resettable for BLK4_W4_SPEC {}
