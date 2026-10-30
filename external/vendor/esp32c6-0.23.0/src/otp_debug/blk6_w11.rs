#[doc = "Register `BLK6_W11` reader"]
pub type R = crate::R<BLK6_W11_SPEC>;
#[doc = "Field `BLOCK6_W11` reader - Otp block6 word11 data."]
pub type BLOCK6_W11_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Otp block6 word11 data."]
    #[inline(always)]
    pub fn block6_w11(&self) -> BLOCK6_W11_R {
        BLOCK6_W11_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BLK6_W11")
            .field("block6_w11", &self.block6_w11())
            .finish()
    }
}
#[doc = "Otp debuger block6 data register11.\n\nYou can [`read`](crate::Reg::read) this register and get [`blk6_w11::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BLK6_W11_SPEC;
impl crate::RegisterSpec for BLK6_W11_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`blk6_w11::R`](R) reader structure"]
impl crate::Readable for BLK6_W11_SPEC {}
#[doc = "`reset()` method sets BLK6_W11 to value 0"]
impl crate::Resettable for BLK6_W11_SPEC {}
