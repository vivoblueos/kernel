#[doc = "Register `L2_CACHE_ACS_FAIL_ADDR` reader"]
pub type R = crate::R<L2_CACHE_ACS_FAIL_ADDR_SPEC>;
#[doc = "Field `L2_CACHE_FAIL_ADDR` reader - The register records the address of fail-access when L1-Cache accesses L2-Cache."]
pub type L2_CACHE_FAIL_ADDR_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - The register records the address of fail-access when L1-Cache accesses L2-Cache."]
    #[inline(always)]
    pub fn l2_cache_fail_addr(&self) -> L2_CACHE_FAIL_ADDR_R {
        L2_CACHE_FAIL_ADDR_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L2_CACHE_ACS_FAIL_ADDR")
            .field("l2_cache_fail_addr", &self.l2_cache_fail_addr())
            .finish()
    }
}
#[doc = "L2-Cache Access Fail Address information register\n\nYou can [`read`](crate::Reg::read) this register and get [`l2_cache_acs_fail_addr::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L2_CACHE_ACS_FAIL_ADDR_SPEC;
impl crate::RegisterSpec for L2_CACHE_ACS_FAIL_ADDR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l2_cache_acs_fail_addr::R`](R) reader structure"]
impl crate::Readable for L2_CACHE_ACS_FAIL_ADDR_SPEC {}
#[doc = "`reset()` method sets L2_CACHE_ACS_FAIL_ADDR to value 0"]
impl crate::Resettable for L2_CACHE_ACS_FAIL_ADDR_SPEC {}
