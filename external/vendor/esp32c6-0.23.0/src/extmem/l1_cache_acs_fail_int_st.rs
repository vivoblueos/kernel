#[doc = "Register `L1_CACHE_ACS_FAIL_INT_ST` reader"]
pub type R = crate::R<L1_CACHE_ACS_FAIL_INT_ST_SPEC>;
#[doc = "Field `L1_ICACHE0_FAIL_INT_ST` reader - The bit indicates the interrupt status of access fail that occurs in L1-ICache0 due to cpu accesses L1-ICache."]
pub type L1_ICACHE0_FAIL_INT_ST_R = crate::BitReader;
#[doc = "Field `L1_ICACHE1_FAIL_INT_ST` reader - The bit indicates the interrupt status of access fail that occurs in L1-ICache1 due to cpu accesses L1-ICache."]
pub type L1_ICACHE1_FAIL_INT_ST_R = crate::BitReader;
#[doc = "Field `L1_ICACHE2_FAIL_INT_ST` reader - Reserved"]
pub type L1_ICACHE2_FAIL_INT_ST_R = crate::BitReader;
#[doc = "Field `L1_ICACHE3_FAIL_INT_ST` reader - Reserved"]
pub type L1_ICACHE3_FAIL_INT_ST_R = crate::BitReader;
#[doc = "Field `L1_CACHE_FAIL_INT_ST` reader - The bit indicates the interrupt status of access fail that occurs in L1-DCache due to cpu accesses L1-DCache."]
pub type L1_CACHE_FAIL_INT_ST_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - The bit indicates the interrupt status of access fail that occurs in L1-ICache0 due to cpu accesses L1-ICache."]
    #[inline(always)]
    pub fn l1_icache0_fail_int_st(&self) -> L1_ICACHE0_FAIL_INT_ST_R {
        L1_ICACHE0_FAIL_INT_ST_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The bit indicates the interrupt status of access fail that occurs in L1-ICache1 due to cpu accesses L1-ICache."]
    #[inline(always)]
    pub fn l1_icache1_fail_int_st(&self) -> L1_ICACHE1_FAIL_INT_ST_R {
        L1_ICACHE1_FAIL_INT_ST_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Reserved"]
    #[inline(always)]
    pub fn l1_icache2_fail_int_st(&self) -> L1_ICACHE2_FAIL_INT_ST_R {
        L1_ICACHE2_FAIL_INT_ST_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Reserved"]
    #[inline(always)]
    pub fn l1_icache3_fail_int_st(&self) -> L1_ICACHE3_FAIL_INT_ST_R {
        L1_ICACHE3_FAIL_INT_ST_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - The bit indicates the interrupt status of access fail that occurs in L1-DCache due to cpu accesses L1-DCache."]
    #[inline(always)]
    pub fn l1_cache_fail_int_st(&self) -> L1_CACHE_FAIL_INT_ST_R {
        L1_CACHE_FAIL_INT_ST_R::new(((self.bits >> 4) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L1_CACHE_ACS_FAIL_INT_ST")
            .field("l1_icache0_fail_int_st", &self.l1_icache0_fail_int_st())
            .field("l1_icache1_fail_int_st", &self.l1_icache1_fail_int_st())
            .field("l1_icache2_fail_int_st", &self.l1_icache2_fail_int_st())
            .field("l1_icache3_fail_int_st", &self.l1_icache3_fail_int_st())
            .field("l1_cache_fail_int_st", &self.l1_cache_fail_int_st())
            .finish()
    }
}
#[doc = "Cache Access Fail Interrupt status register\n\nYou can [`read`](crate::Reg::read) this register and get [`l1_cache_acs_fail_int_st::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L1_CACHE_ACS_FAIL_INT_ST_SPEC;
impl crate::RegisterSpec for L1_CACHE_ACS_FAIL_INT_ST_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l1_cache_acs_fail_int_st::R`](R) reader structure"]
impl crate::Readable for L1_CACHE_ACS_FAIL_INT_ST_SPEC {}
#[doc = "`reset()` method sets L1_CACHE_ACS_FAIL_INT_ST to value 0"]
impl crate::Resettable for L1_CACHE_ACS_FAIL_INT_ST_SPEC {}
