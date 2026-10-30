#[doc = "Register `UTIME` reader"]
pub type R = crate::R<UTIME_SPEC>;
#[doc = "Field `UTIME` reader - Represents the read-only 64-bit CLINT timer counter value."]
pub type UTIME_R = crate::FieldReader<u64>;
impl R {
    #[doc = "Bits 0:63 - Represents the read-only 64-bit CLINT timer counter value."]
    #[inline(always)]
    pub fn utime(&self) -> UTIME_R {
        UTIME_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("UTIME")
            .field("utime", &self.utime())
            .finish()
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`utime::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct UTIME_SPEC;
impl crate::RegisterSpec for UTIME_SPEC {
    type Ux = u64;
}
#[doc = "`read()` method returns [`utime::R`](R) reader structure"]
impl crate::Readable for UTIME_SPEC {}
#[doc = "`reset()` method sets UTIME to value 0"]
impl crate::Resettable for UTIME_SPEC {}
