#[doc = "Register `LOCK_STATUS` reader"]
pub type R = crate::R<LOCK_STATUS_SPEC>;
#[doc = "Field `LOCK_STATUS` reader - read hareware lock status for debug"]
pub type LOCK_STATUS_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:1 - read hareware lock status for debug"]
    #[inline(always)]
    pub fn lock_status(&self) -> LOCK_STATUS_R {
        LOCK_STATUS_R::new((self.bits & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("LOCK_STATUS")
            .field("lock_status", &self.lock_status())
            .finish()
    }
}
#[doc = "lock status regsiter\n\nYou can [`read`](crate::Reg::read) this register and get [`lock_status::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LOCK_STATUS_SPEC;
impl crate::RegisterSpec for LOCK_STATUS_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`lock_status::R`](R) reader structure"]
impl crate::Readable for LOCK_STATUS_SPEC {}
#[doc = "`reset()` method sets LOCK_STATUS to value 0"]
impl crate::Resettable for LOCK_STATUS_SPEC {}
