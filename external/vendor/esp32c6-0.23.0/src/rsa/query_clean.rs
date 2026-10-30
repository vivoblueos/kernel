#[doc = "Register `QUERY_CLEAN` reader"]
pub type R = crate::R<QUERY_CLEAN_SPEC>;
#[doc = "Field `QUERY_CLEAN` reader - query clean"]
pub type QUERY_CLEAN_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - query clean"]
    #[inline(always)]
    pub fn query_clean(&self) -> QUERY_CLEAN_R {
        QUERY_CLEAN_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("QUERY_CLEAN")
            .field("query_clean", &self.query_clean())
            .finish()
    }
}
#[doc = "RSA query clean register\n\nYou can [`read`](crate::Reg::read) this register and get [`query_clean::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct QUERY_CLEAN_SPEC;
impl crate::RegisterSpec for QUERY_CLEAN_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`query_clean::R`](R) reader structure"]
impl crate::Readable for QUERY_CLEAN_SPEC {}
#[doc = "`reset()` method sets QUERY_CLEAN to value 0"]
impl crate::Resettable for QUERY_CLEAN_SPEC {}
