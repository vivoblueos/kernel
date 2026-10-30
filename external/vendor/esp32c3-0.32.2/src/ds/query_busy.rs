#[doc = "Register `QUERY_BUSY` reader"]
pub type R = crate::R<QUERY_BUSY_SPEC>;
#[doc = "Field `QUERY_BUSY` reader - digital signature state. 1'b0: idle, 1'b1: busy"]
pub type QUERY_BUSY_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - digital signature state. 1'b0: idle, 1'b1: busy"]
    #[inline(always)]
    pub fn query_busy(&self) -> QUERY_BUSY_R {
        QUERY_BUSY_R::new((self.bits & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("QUERY_BUSY")
            .field("query_busy", &self.query_busy())
            .finish()
    }
}
#[doc = "DS query busy register\n\nYou can [`read`](crate::Reg::read) this register and get [`query_busy::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct QUERY_BUSY_SPEC;
impl crate::RegisterSpec for QUERY_BUSY_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`query_busy::R`](R) reader structure"]
impl crate::Readable for QUERY_BUSY_SPEC {}
#[doc = "`reset()` method sets QUERY_BUSY to value 0"]
impl crate::Resettable for QUERY_BUSY_SPEC {}
