#[doc = "Register `EXCEPTION_INFO0` reader"]
pub type R = crate::R<EXCEPTION_INFO0_SPEC>;
#[doc = "Field `EXCEPTION_REGION` reader - Exception region"]
pub type EXCEPTION_REGION_R = crate::FieldReader;
#[doc = "Field `EXCEPTION_MODE` reader - Exception mode"]
pub type EXCEPTION_MODE_R = crate::FieldReader;
#[doc = "Field `EXCEPTION_ID` reader - Exception id information"]
pub type EXCEPTION_ID_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:3 - Exception region"]
    #[inline(always)]
    pub fn exception_region(&self) -> EXCEPTION_REGION_R {
        EXCEPTION_REGION_R::new((self.bits & 0x0f) as u8)
    }
    #[doc = "Bits 16:17 - Exception mode"]
    #[inline(always)]
    pub fn exception_mode(&self) -> EXCEPTION_MODE_R {
        EXCEPTION_MODE_R::new(((self.bits >> 16) & 3) as u8)
    }
    #[doc = "Bits 18:22 - Exception id information"]
    #[inline(always)]
    pub fn exception_id(&self) -> EXCEPTION_ID_R {
        EXCEPTION_ID_R::new(((self.bits >> 18) & 0x1f) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("EXCEPTION_INFO0")
            .field("exception_region", &self.exception_region())
            .field("exception_mode", &self.exception_mode())
            .field("exception_id", &self.exception_id())
            .finish()
    }
}
#[doc = "M0 exception_info0 register\n\nYou can [`read`](crate::Reg::read) this register and get [`exception_info0::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct EXCEPTION_INFO0_SPEC;
impl crate::RegisterSpec for EXCEPTION_INFO0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`exception_info0::R`](R) reader structure"]
impl crate::Readable for EXCEPTION_INFO0_SPEC {}
#[doc = "`reset()` method sets EXCEPTION_INFO0 to value 0"]
impl crate::Resettable for EXCEPTION_INFO0_SPEC {}
