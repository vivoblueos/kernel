#[doc = "Register `L2_CACHE_SYNC_PRELOAD_INT_ENA` reader"]
pub type R = crate::R<L2_CACHE_SYNC_PRELOAD_INT_ENA_SPEC>;
#[doc = "Field `L2_CACHE_PLD_DONE_INT_ENA` reader - The bit is used to enable interrupt of L2-Cache preload-operation done."]
pub type L2_CACHE_PLD_DONE_INT_ENA_R = crate::BitReader;
#[doc = "Field `L2_CACHE_PLD_ERR_INT_ENA` reader - The bit is used to enable interrupt of L2-Cache preload-operation error."]
pub type L2_CACHE_PLD_ERR_INT_ENA_R = crate::BitReader;
impl R {
    #[doc = "Bit 5 - The bit is used to enable interrupt of L2-Cache preload-operation done."]
    #[inline(always)]
    pub fn l2_cache_pld_done_int_ena(&self) -> L2_CACHE_PLD_DONE_INT_ENA_R {
        L2_CACHE_PLD_DONE_INT_ENA_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 12 - The bit is used to enable interrupt of L2-Cache preload-operation error."]
    #[inline(always)]
    pub fn l2_cache_pld_err_int_ena(&self) -> L2_CACHE_PLD_ERR_INT_ENA_R {
        L2_CACHE_PLD_ERR_INT_ENA_R::new(((self.bits >> 12) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L2_CACHE_SYNC_PRELOAD_INT_ENA")
            .field(
                "l2_cache_pld_done_int_ena",
                &self.l2_cache_pld_done_int_ena(),
            )
            .field("l2_cache_pld_err_int_ena", &self.l2_cache_pld_err_int_ena())
            .finish()
    }
}
#[doc = "L1-Cache Access Fail Interrupt enable register\n\nYou can [`read`](crate::Reg::read) this register and get [`l2_cache_sync_preload_int_ena::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L2_CACHE_SYNC_PRELOAD_INT_ENA_SPEC;
impl crate::RegisterSpec for L2_CACHE_SYNC_PRELOAD_INT_ENA_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l2_cache_sync_preload_int_ena::R`](R) reader structure"]
impl crate::Readable for L2_CACHE_SYNC_PRELOAD_INT_ENA_SPEC {}
#[doc = "`reset()` method sets L2_CACHE_SYNC_PRELOAD_INT_ENA to value 0"]
impl crate::Resettable for L2_CACHE_SYNC_PRELOAD_INT_ENA_SPEC {}
