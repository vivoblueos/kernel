#[doc = "Register `BLK10_W9` reader"]
pub type R = crate::R<BLK10_W9_SPEC>;
#[doc = "Field `BLOCK10_W9` reader - Otp block10 word9 data."]
pub type BLOCK10_W9_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Otp block10 word9 data."]
    #[inline(always)]
    pub fn block10_w9(&self) -> BLOCK10_W9_R {
        BLOCK10_W9_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("BLK10_W9")
            .field("block10_w9", &self.block10_w9())
            .finish()
    }
}
#[doc = "Otp debuger block10 data register9.\n\nYou can [`read`](crate::Reg::read) this register and get [`blk10_w9::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BLK10_W9_SPEC;
impl crate::RegisterSpec for BLK10_W9_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`blk10_w9::R`](R) reader structure"]
impl crate::Readable for BLK10_W9_SPEC {}
#[doc = "`reset()` method sets BLK10_W9 to value 0"]
impl crate::Resettable for BLK10_W9_SPEC {}
