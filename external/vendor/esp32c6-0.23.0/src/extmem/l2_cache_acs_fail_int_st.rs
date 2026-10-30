#[doc = "Register `L2_CACHE_ACS_FAIL_INT_ST` reader"]
pub type R = crate::R<L2_CACHE_ACS_FAIL_INT_ST_SPEC>;
#[doc = "Field `L2_CACHE_FAIL_INT_ST` reader - The bit indicates the interrupt status of access fail that occurs in L2-Cache due to l1 cache accesses L2-Cache."]
pub type L2_CACHE_FAIL_INT_ST_R = crate::BitReader;
impl R {
    #[doc = "Bit 5 - The bit indicates the interrupt status of access fail that occurs in L2-Cache due to l1 cache accesses L2-Cache."]
    #[inline(always)]
    pub fn l2_cache_fail_int_st(&self) -> L2_CACHE_FAIL_INT_ST_R {
        L2_CACHE_FAIL_INT_ST_R::new(((self.bits >> 5) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L2_CACHE_ACS_FAIL_INT_ST")
            .field("l2_cache_fail_int_st", &self.l2_cache_fail_int_st())
            .finish()
    }
}
#[doc = "Cache Access Fail Interrupt status register\n\nYou can [`read`](crate::Reg::read) this register and get [`l2_cache_acs_fail_int_st::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L2_CACHE_ACS_FAIL_INT_ST_SPEC;
impl crate::RegisterSpec for L2_CACHE_ACS_FAIL_INT_ST_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l2_cache_acs_fail_int_st::R`](R) reader structure"]
impl crate::Readable for L2_CACHE_ACS_FAIL_INT_ST_SPEC {}
#[doc = "`reset()` method sets L2_CACHE_ACS_FAIL_INT_ST to value 0"]
impl crate::Resettable for L2_CACHE_ACS_FAIL_INT_ST_SPEC {}
