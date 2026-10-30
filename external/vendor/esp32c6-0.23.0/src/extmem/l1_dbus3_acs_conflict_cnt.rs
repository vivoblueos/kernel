#[doc = "Register `L1_DBUS3_ACS_CONFLICT_CNT` reader"]
pub type R = crate::R<L1_DBUS3_ACS_CONFLICT_CNT_SPEC>;
#[doc = "Field `L1_DBUS3_CONFLICT_CNT` reader - The register records the number of access-conflicts when bus3 accesses L1-DCache."]
pub type L1_DBUS3_CONFLICT_CNT_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - The register records the number of access-conflicts when bus3 accesses L1-DCache."]
    #[inline(always)]
    pub fn l1_dbus3_conflict_cnt(&self) -> L1_DBUS3_CONFLICT_CNT_R {
        L1_DBUS3_CONFLICT_CNT_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L1_DBUS3_ACS_CONFLICT_CNT")
            .field("l1_dbus3_conflict_cnt", &self.l1_dbus3_conflict_cnt())
            .finish()
    }
}
#[doc = "L1-DCache bus3 Conflict-Access Counter register\n\nYou can [`read`](crate::Reg::read) this register and get [`l1_dbus3_acs_conflict_cnt::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L1_DBUS3_ACS_CONFLICT_CNT_SPEC;
impl crate::RegisterSpec for L1_DBUS3_ACS_CONFLICT_CNT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l1_dbus3_acs_conflict_cnt::R`](R) reader structure"]
impl crate::Readable for L1_DBUS3_ACS_CONFLICT_CNT_SPEC {}
#[doc = "`reset()` method sets L1_DBUS3_ACS_CONFLICT_CNT to value 0"]
impl crate::Resettable for L1_DBUS3_ACS_CONFLICT_CNT_SPEC {}
