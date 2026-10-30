#[doc = "Register `L2_CACHE_SYNC_PRELOAD_EXCEPTION` reader"]
pub type R = crate::R<L2_CACHE_SYNC_PRELOAD_EXCEPTION_SPEC>;
#[doc = "Field `L2_CACHE_PLD_ERR_CODE` reader - The value 2 is Only available which means preload size is error in L2-Cache."]
pub type L2_CACHE_PLD_ERR_CODE_R = crate::FieldReader;
impl R {
    #[doc = "Bits 10:11 - The value 2 is Only available which means preload size is error in L2-Cache."]
    #[inline(always)]
    pub fn l2_cache_pld_err_code(&self) -> L2_CACHE_PLD_ERR_CODE_R {
        L2_CACHE_PLD_ERR_CODE_R::new(((self.bits >> 10) & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L2_CACHE_SYNC_PRELOAD_EXCEPTION")
            .field("l2_cache_pld_err_code", &self.l2_cache_pld_err_code())
            .finish()
    }
}
#[doc = "Cache Sync/Preload Operation exception register\n\nYou can [`read`](crate::Reg::read) this register and get [`l2_cache_sync_preload_exception::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L2_CACHE_SYNC_PRELOAD_EXCEPTION_SPEC;
impl crate::RegisterSpec for L2_CACHE_SYNC_PRELOAD_EXCEPTION_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l2_cache_sync_preload_exception::R`](R) reader structure"]
impl crate::Readable for L2_CACHE_SYNC_PRELOAD_EXCEPTION_SPEC {}
#[doc = "`reset()` method sets L2_CACHE_SYNC_PRELOAD_EXCEPTION to value 0"]
impl crate::Resettable for L2_CACHE_SYNC_PRELOAD_EXCEPTION_SPEC {}
