#[doc = "Register `STRAP` reader"]
pub type R = crate::R<STRAP_SPEC>;
#[doc = "Field `STRAPPING` reader - pad strapping register"]
pub type STRAPPING_R = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:15 - pad strapping register"]
    #[inline(always)]
    pub fn strapping(&self) -> STRAPPING_R {
        STRAPPING_R::new((self.bits & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("STRAP")
            .field("strapping", &self.strapping())
            .finish()
    }
}
#[doc = "pad strapping register\n\nYou can [`read`](crate::Reg::read) this register and get [`strap::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct STRAP_SPEC;
impl crate::RegisterSpec for STRAP_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`strap::R`](R) reader structure"]
impl crate::Readable for STRAP_SPEC {}
#[doc = "`reset()` method sets STRAP to value 0"]
impl crate::Resettable for STRAP_SPEC {}
