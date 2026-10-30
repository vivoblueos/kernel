#[doc = "Register `L1_CACHE_SYNC_PRELOAD_INT_ST` reader"]
pub type R = crate::R<L1_CACHE_SYNC_PRELOAD_INT_ST_SPEC>;
#[doc = "Field `L1_ICACHE0_PLD_DONE_INT_ST` reader - The bit indicates the status of the interrupt that occurs only when L1-ICache0 preload-operation is done."]
pub type L1_ICACHE0_PLD_DONE_INT_ST_R = crate::BitReader;
#[doc = "Field `L1_ICACHE1_PLD_DONE_INT_ST` reader - The bit indicates the status of the interrupt that occurs only when L1-ICache1 preload-operation is done."]
pub type L1_ICACHE1_PLD_DONE_INT_ST_R = crate::BitReader;
#[doc = "Field `L1_ICACHE2_PLD_DONE_INT_ST` reader - Reserved"]
pub type L1_ICACHE2_PLD_DONE_INT_ST_R = crate::BitReader;
#[doc = "Field `L1_ICACHE3_PLD_DONE_INT_ST` reader - Reserved"]
pub type L1_ICACHE3_PLD_DONE_INT_ST_R = crate::BitReader;
#[doc = "Field `L1_CACHE_PLD_DONE_INT_ST` reader - The bit indicates the status of the interrupt that occurs only when L1-Cache preload-operation is done."]
pub type L1_CACHE_PLD_DONE_INT_ST_R = crate::BitReader;
#[doc = "Field `CACHE_SYNC_DONE_INT_ST` reader - The bit indicates the status of the interrupt that occurs only when Cache sync-operation is done."]
pub type CACHE_SYNC_DONE_INT_ST_R = crate::BitReader;
#[doc = "Field `L1_ICACHE0_PLD_ERR_INT_ST` reader - The bit indicates the status of the interrupt of L1-ICache0 preload-operation error."]
pub type L1_ICACHE0_PLD_ERR_INT_ST_R = crate::BitReader;
#[doc = "Field `L1_ICACHE1_PLD_ERR_INT_ST` reader - The bit indicates the status of the interrupt of L1-ICache1 preload-operation error."]
pub type L1_ICACHE1_PLD_ERR_INT_ST_R = crate::BitReader;
#[doc = "Field `L1_ICACHE2_PLD_ERR_INT_ST` reader - Reserved"]
pub type L1_ICACHE2_PLD_ERR_INT_ST_R = crate::BitReader;
#[doc = "Field `L1_ICACHE3_PLD_ERR_INT_ST` reader - Reserved"]
pub type L1_ICACHE3_PLD_ERR_INT_ST_R = crate::BitReader;
#[doc = "Field `L1_CACHE_PLD_ERR_INT_ST` reader - The bit indicates the status of the interrupt of L1-Cache preload-operation error."]
pub type L1_CACHE_PLD_ERR_INT_ST_R = crate::BitReader;
#[doc = "Field `CACHE_SYNC_ERR_INT_ST` reader - The bit indicates the status of the interrupt of Cache sync-operation error."]
pub type CACHE_SYNC_ERR_INT_ST_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - The bit indicates the status of the interrupt that occurs only when L1-ICache0 preload-operation is done."]
    #[inline(always)]
    pub fn l1_icache0_pld_done_int_st(&self) -> L1_ICACHE0_PLD_DONE_INT_ST_R {
        L1_ICACHE0_PLD_DONE_INT_ST_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The bit indicates the status of the interrupt that occurs only when L1-ICache1 preload-operation is done."]
    #[inline(always)]
    pub fn l1_icache1_pld_done_int_st(&self) -> L1_ICACHE1_PLD_DONE_INT_ST_R {
        L1_ICACHE1_PLD_DONE_INT_ST_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Reserved"]
    #[inline(always)]
    pub fn l1_icache2_pld_done_int_st(&self) -> L1_ICACHE2_PLD_DONE_INT_ST_R {
        L1_ICACHE2_PLD_DONE_INT_ST_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Reserved"]
    #[inline(always)]
    pub fn l1_icache3_pld_done_int_st(&self) -> L1_ICACHE3_PLD_DONE_INT_ST_R {
        L1_ICACHE3_PLD_DONE_INT_ST_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - The bit indicates the status of the interrupt that occurs only when L1-Cache preload-operation is done."]
    #[inline(always)]
    pub fn l1_cache_pld_done_int_st(&self) -> L1_CACHE_PLD_DONE_INT_ST_R {
        L1_CACHE_PLD_DONE_INT_ST_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 6 - The bit indicates the status of the interrupt that occurs only when Cache sync-operation is done."]
    #[inline(always)]
    pub fn cache_sync_done_int_st(&self) -> CACHE_SYNC_DONE_INT_ST_R {
        CACHE_SYNC_DONE_INT_ST_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - The bit indicates the status of the interrupt of L1-ICache0 preload-operation error."]
    #[inline(always)]
    pub fn l1_icache0_pld_err_int_st(&self) -> L1_ICACHE0_PLD_ERR_INT_ST_R {
        L1_ICACHE0_PLD_ERR_INT_ST_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - The bit indicates the status of the interrupt of L1-ICache1 preload-operation error."]
    #[inline(always)]
    pub fn l1_icache1_pld_err_int_st(&self) -> L1_ICACHE1_PLD_ERR_INT_ST_R {
        L1_ICACHE1_PLD_ERR_INT_ST_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Reserved"]
    #[inline(always)]
    pub fn l1_icache2_pld_err_int_st(&self) -> L1_ICACHE2_PLD_ERR_INT_ST_R {
        L1_ICACHE2_PLD_ERR_INT_ST_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Reserved"]
    #[inline(always)]
    pub fn l1_icache3_pld_err_int_st(&self) -> L1_ICACHE3_PLD_ERR_INT_ST_R {
        L1_ICACHE3_PLD_ERR_INT_ST_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - The bit indicates the status of the interrupt of L1-Cache preload-operation error."]
    #[inline(always)]
    pub fn l1_cache_pld_err_int_st(&self) -> L1_CACHE_PLD_ERR_INT_ST_R {
        L1_CACHE_PLD_ERR_INT_ST_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 13 - The bit indicates the status of the interrupt of Cache sync-operation error."]
    #[inline(always)]
    pub fn cache_sync_err_int_st(&self) -> CACHE_SYNC_ERR_INT_ST_R {
        CACHE_SYNC_ERR_INT_ST_R::new(((self.bits >> 13) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L1_CACHE_SYNC_PRELOAD_INT_ST")
            .field(
                "l1_icache0_pld_done_int_st",
                &self.l1_icache0_pld_done_int_st(),
            )
            .field(
                "l1_icache1_pld_done_int_st",
                &self.l1_icache1_pld_done_int_st(),
            )
            .field(
                "l1_icache2_pld_done_int_st",
                &self.l1_icache2_pld_done_int_st(),
            )
            .field(
                "l1_icache3_pld_done_int_st",
                &self.l1_icache3_pld_done_int_st(),
            )
            .field("l1_cache_pld_done_int_st", &self.l1_cache_pld_done_int_st())
            .field("cache_sync_done_int_st", &self.cache_sync_done_int_st())
            .field(
                "l1_icache0_pld_err_int_st",
                &self.l1_icache0_pld_err_int_st(),
            )
            .field(
                "l1_icache1_pld_err_int_st",
                &self.l1_icache1_pld_err_int_st(),
            )
            .field(
                "l1_icache2_pld_err_int_st",
                &self.l1_icache2_pld_err_int_st(),
            )
            .field(
                "l1_icache3_pld_err_int_st",
                &self.l1_icache3_pld_err_int_st(),
            )
            .field("l1_cache_pld_err_int_st", &self.l1_cache_pld_err_int_st())
            .field("cache_sync_err_int_st", &self.cache_sync_err_int_st())
            .finish()
    }
}
#[doc = "L1-Cache Access Fail Interrupt status register\n\nYou can [`read`](crate::Reg::read) this register and get [`l1_cache_sync_preload_int_st::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L1_CACHE_SYNC_PRELOAD_INT_ST_SPEC;
impl crate::RegisterSpec for L1_CACHE_SYNC_PRELOAD_INT_ST_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l1_cache_sync_preload_int_st::R`](R) reader structure"]
impl crate::Readable for L1_CACHE_SYNC_PRELOAD_INT_ST_SPEC {}
#[doc = "`reset()` method sets L1_CACHE_SYNC_PRELOAD_INT_ST to value 0"]
impl crate::Resettable for L1_CACHE_SYNC_PRELOAD_INT_ST_SPEC {}
