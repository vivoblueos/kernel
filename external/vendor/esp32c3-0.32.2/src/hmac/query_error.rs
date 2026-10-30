#[doc = "Register `QUERY_ERROR` reader"]
pub type R = crate::R<QUERY_ERROR_SPEC>;
#[doc = "Field `QUERY_CHECK` reader - Hmac configuration state. 0: key are agree with purpose. 1: error"]
pub type QUERY_CHECK_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - Hmac configuration state. 0: key are agree with purpose. 1: error"]
    #[inline(always)]
    pub fn query_check(&self) -> QUERY_CHECK_R {
        QUERY_CHECK_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("QUERY_ERROR")
            .field("query_check", &self.query_check())
            .finish()
    }
}
#[doc = "Error register.\n\nYou can [`read`](crate::Reg::read) this register and get [`query_error::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct QUERY_ERROR_SPEC;
impl crate::RegisterSpec for QUERY_ERROR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`query_error::R`](R) reader structure"]
impl crate::Readable for QUERY_ERROR_SPEC {}
#[doc = "`reset()` method sets QUERY_ERROR to value 0"]
impl crate::Resettable for QUERY_ERROR_SPEC {}
