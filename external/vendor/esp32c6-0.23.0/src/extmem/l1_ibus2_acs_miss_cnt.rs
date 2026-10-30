#[doc = "Register `L1_IBUS2_ACS_MISS_CNT` reader"]
pub type R = crate::R<L1_IBUS2_ACS_MISS_CNT_SPEC>;
#[doc = "Field `L1_IBUS2_MISS_CNT` reader - The register records the number of missing when bus2 accesses L1-ICache2."]
pub type L1_IBUS2_MISS_CNT_R = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - The register records the number of missing when bus2 accesses L1-ICache2."]
    #[inline(always)]
    pub fn l1_ibus2_miss_cnt(&self) -> L1_IBUS2_MISS_CNT_R {
        L1_IBUS2_MISS_CNT_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L1_IBUS2_ACS_MISS_CNT")
            .field("l1_ibus2_miss_cnt", &self.l1_ibus2_miss_cnt())
            .finish()
    }
}
#[doc = "L1-ICache bus2 Miss-Access Counter register\n\nYou can [`read`](crate::Reg::read) this register and get [`l1_ibus2_acs_miss_cnt::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L1_IBUS2_ACS_MISS_CNT_SPEC;
impl crate::RegisterSpec for L1_IBUS2_ACS_MISS_CNT_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l1_ibus2_acs_miss_cnt::R`](R) reader structure"]
impl crate::Readable for L1_IBUS2_ACS_MISS_CNT_SPEC {}
#[doc = "`reset()` method sets L1_IBUS2_ACS_MISS_CNT to value 0"]
impl crate::Resettable for L1_IBUS2_ACS_MISS_CNT_SPEC {}
