#[doc = "Register `L1_ICACHE1_ACS_FAIL_ID_ATTR` reader"]
pub type R = crate::R<L1_ICACHE1_ACS_FAIL_ID_ATTR_SPEC>;
#[doc = "Field `L1_ICACHE1_FAIL_ID` reader - The register records the ID of fail-access when cache1 accesses L1-ICache."]
pub type L1_ICACHE1_FAIL_ID_R = crate::FieldReader<u16>;
#[doc = "Field `L1_ICACHE1_FAIL_ATTR` reader - The register records the attribution of fail-access when cache1 accesses L1-ICache."]
pub type L1_ICACHE1_FAIL_ATTR_R = crate::FieldReader<u16>;
impl R {
    #[doc = "Bits 0:15 - The register records the ID of fail-access when cache1 accesses L1-ICache."]
    #[inline(always)]
    pub fn l1_icache1_fail_id(&self) -> L1_ICACHE1_FAIL_ID_R {
        L1_ICACHE1_FAIL_ID_R::new((self.bits & 0xffff) as u16)
    }
    #[doc = "Bits 16:31 - The register records the attribution of fail-access when cache1 accesses L1-ICache."]
    #[inline(always)]
    pub fn l1_icache1_fail_attr(&self) -> L1_ICACHE1_FAIL_ATTR_R {
        L1_ICACHE1_FAIL_ATTR_R::new(((self.bits >> 16) & 0xffff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L1_ICACHE1_ACS_FAIL_ID_ATTR")
            .field("l1_icache1_fail_id", &self.l1_icache1_fail_id())
            .field("l1_icache1_fail_attr", &self.l1_icache1_fail_attr())
            .finish()
    }
}
#[doc = "L1-ICache0 Access Fail ID/attribution information register\n\nYou can [`read`](crate::Reg::read) this register and get [`l1_icache1_acs_fail_id_attr::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L1_ICACHE1_ACS_FAIL_ID_ATTR_SPEC;
impl crate::RegisterSpec for L1_ICACHE1_ACS_FAIL_ID_ATTR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l1_icache1_acs_fail_id_attr::R`](R) reader structure"]
impl crate::Readable for L1_ICACHE1_ACS_FAIL_ID_ATTR_SPEC {}
#[doc = "`reset()` method sets L1_ICACHE1_ACS_FAIL_ID_ATTR to value 0"]
impl crate::Resettable for L1_ICACHE1_ACS_FAIL_ID_ATTR_SPEC {}
