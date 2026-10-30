#[doc = "Register `RD_KEY4_DATA3` reader"]
pub type R = crate::R<RD_KEY4_DATA3_SPEC>;
#[doc = "Field `KEY4_DATA3` reader - Stores the third 32 bits of KEY4."]
pub type KEY4_DATA3_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Stores the third 32 bits of KEY4."]
    #[inline(always)]
    pub fn key4_data3(&self) -> KEY4_DATA3_R {
        KEY4_DATA3_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RD_KEY4_DATA3")
            .field("key4_data3", &self.key4_data3())
            .finish()
    }
}
#[doc = "Register 3 of BLOCK8 (KEY4).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key4_data3::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RD_KEY4_DATA3_SPEC;
impl crate::RegisterSpec for RD_KEY4_DATA3_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rd_key4_data3::R`](R) reader structure"]
impl crate::Readable for RD_KEY4_DATA3_SPEC {}
#[doc = "`reset()` method sets RD_KEY4_DATA3 to value 0"]
impl crate::Resettable for RD_KEY4_DATA3_SPEC {}
