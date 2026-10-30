#[doc = "Register `RD_KEY2_DATA5` reader"]
pub type R = crate::R<RD_KEY2_DATA5_SPEC>;
#[doc = "Field `KEY2_DATA5` reader - Stores the fifth 32 bits of KEY2."]
pub type KEY2_DATA5_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Stores the fifth 32 bits of KEY2."]
    #[inline(always)]
    pub fn key2_data5(&self) -> KEY2_DATA5_R {
        KEY2_DATA5_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RD_KEY2_DATA5")
            .field("key2_data5", &self.key2_data5())
            .finish()
    }
}
#[doc = "Register $n of BLOCK6 (KEY2).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key2_data5::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RD_KEY2_DATA5_SPEC;
impl crate::RegisterSpec for RD_KEY2_DATA5_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rd_key2_data5::R`](R) reader structure"]
impl crate::Readable for RD_KEY2_DATA5_SPEC {}
#[doc = "`reset()` method sets RD_KEY2_DATA5 to value 0"]
impl crate::Resettable for RD_KEY2_DATA5_SPEC {}
