#[doc = "Register `RD_KEY1_DATA6` reader"]
pub type R = crate::R<RD_KEY1_DATA6_SPEC>;
#[doc = "Field `KEY1_DATA6` reader - Stores the sixth 32 bits of KEY1."]
pub type KEY1_DATA6_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Stores the sixth 32 bits of KEY1."]
    #[inline(always)]
    pub fn key1_data6(&self) -> KEY1_DATA6_R {
        KEY1_DATA6_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RD_KEY1_DATA6")
            .field("key1_data6", &self.key1_data6())
            .finish()
    }
}
#[doc = "Register 6 of BLOCK5 (KEY1).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key1_data6::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RD_KEY1_DATA6_SPEC;
impl crate::RegisterSpec for RD_KEY1_DATA6_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rd_key1_data6::R`](R) reader structure"]
impl crate::Readable for RD_KEY1_DATA6_SPEC {}
#[doc = "`reset()` method sets RD_KEY1_DATA6 to value 0"]
impl crate::Resettable for RD_KEY1_DATA6_SPEC {}
