#[doc = "Register `BLK8_W10` reader"]
pub type R = crate::R<BLK8_W10_SPEC>;
#[doc = "Field `BLOCK8_W10` reader - Otp block8 word10 data."]
pub type BLOCK8_W10_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Otp block8 word10 data."]
    #[inline(always)]
    pub fn block8_w10(&self) -> BLOCK8_W10_R {
        BLOCK8_W10_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BLK8_W10")
            .field("block8_w10", &self.block8_w10())
            .finish()
    }
}
#[doc = "Otp debuger block8 data register10.\n\nYou can [`read`](crate::Reg::read) this register and get [`blk8_w10::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BLK8_W10_SPEC;
impl crate::RegisterSpec for BLK8_W10_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`blk8_w10::R`](R) reader structure"]
impl crate::Readable for BLK8_W10_SPEC {}
#[doc = "`reset()` method sets BLK8_W10 to value 0"]
impl crate::Resettable for BLK8_W10_SPEC {}
