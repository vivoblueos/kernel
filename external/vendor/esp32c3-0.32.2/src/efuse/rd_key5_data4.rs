#[doc = "Register `RD_KEY5_DATA4` reader"]
pub type R = crate::R<RD_KEY5_DATA4_SPEC>;
#[doc = "Field `KEY5_DATA4` reader - Stores the fourth 32 bits of KEY5."]
pub type KEY5_DATA4_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - Stores the fourth 32 bits of KEY5."]
    #[inline(always)]
    pub fn key5_data4(&self) -> KEY5_DATA4_R {
        KEY5_DATA4_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("RD_KEY5_DATA4")
            .field("key5_data4", &self.key5_data4())
            .finish()
    }
}
#[doc = "Register 4 of BLOCK9 (KEY5).\n\nYou can [`read`](crate::Reg::read) this register and get [`rd_key5_data4::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RD_KEY5_DATA4_SPEC;
impl crate::RegisterSpec for RD_KEY5_DATA4_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rd_key5_data4::R`](R) reader structure"]
impl crate::Readable for RD_KEY5_DATA4_SPEC {}
#[doc = "`reset()` method sets RD_KEY5_DATA4 to value 0"]
impl crate::Resettable for RD_KEY5_DATA4_SPEC {}
