#[doc = "Register `DBUS_ACS_CNT` reader"]
pub type R = crate::R<DBUS_ACS_CNT_SPEC>;
#[doc = "Field `DBUS_ACS_CNT` reader - The bits are used to count the number of dbus access flash through icache."]
pub type DBUS_ACS_CNT_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - The bits are used to count the number of dbus access flash through icache."]
    #[inline(always)]
    pub fn dbus_acs_cnt(&self) -> DBUS_ACS_CNT_R {
        DBUS_ACS_CNT_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("DBUS_ACS_CNT")
            .field("dbus_acs_cnt", &self.dbus_acs_cnt())
            .finish()
    }
}
#[doc = "This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`dbus_acs_cnt::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DBUS_ACS_CNT_SPEC;
impl crate::RegisterSpec for DBUS_ACS_CNT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dbus_acs_cnt::R`](R) reader structure"]
impl crate::Readable for DBUS_ACS_CNT_SPEC {}
#[doc = "`reset()` method sets DBUS_ACS_CNT to value 0"]
impl crate::Resettable for DBUS_ACS_CNT_SPEC {}
