#[doc = "Register `QUERY_KEY_WRONG` reader"]
pub type R = crate::R<QUERY_KEY_WRONG_SPEC>;
#[doc = "Field `QUERY_KEY_WRONG` reader - digital signature key wrong counter"]
pub type QUERY_KEY_WRONG_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:3 - digital signature key wrong counter"]
    #[inline(always)]
    pub fn query_key_wrong(&self) -> QUERY_KEY_WRONG_R {
        QUERY_KEY_WRONG_R::new((self.bits & 0x0f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("QUERY_KEY_WRONG")
            .field("query_key_wrong", &self.query_key_wrong())
            .finish()
    }
}
#[doc = "DS query key-wrong counter register\n\nYou can [`read`](crate::Reg::read) this register and get [`query_key_wrong::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct QUERY_KEY_WRONG_SPEC;
impl crate::RegisterSpec for QUERY_KEY_WRONG_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`query_key_wrong::R`](R) reader structure"]
impl crate::Readable for QUERY_KEY_WRONG_SPEC {}
#[doc = "`reset()` method sets QUERY_KEY_WRONG to value 0"]
impl crate::Resettable for QUERY_KEY_WRONG_SPEC {}
