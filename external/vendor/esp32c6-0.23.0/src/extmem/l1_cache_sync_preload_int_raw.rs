#[doc = "Register `L1_CACHE_SYNC_PRELOAD_INT_RAW` reader"]
pub type R = crate::R<L1_CACHE_SYNC_PRELOAD_INT_RAW_SPEC>;
#[doc = "Register `L1_CACHE_SYNC_PRELOAD_INT_RAW` writer"]
pub type W = crate::W<L1_CACHE_SYNC_PRELOAD_INT_RAW_SPEC>;
#[doc = "Field `L1_ICACHE0_PLD_DONE_INT_RAW` reader - The raw bit of the interrupt that occurs only when L1-ICache0 preload-operation is done."]
pub type L1_ICACHE0_PLD_DONE_INT_RAW_R = crate::BitReader;
#[doc = "Field `L1_ICACHE0_PLD_DONE_INT_RAW` writer - The raw bit of the interrupt that occurs only when L1-ICache0 preload-operation is done."]
pub type L1_ICACHE0_PLD_DONE_INT_RAW_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `L1_ICACHE1_PLD_DONE_INT_RAW` reader - The raw bit of the interrupt that occurs only when L1-ICache1 preload-operation is done."]
pub type L1_ICACHE1_PLD_DONE_INT_RAW_R = crate::BitReader;
#[doc = "Field `L1_ICACHE1_PLD_DONE_INT_RAW` writer - The raw bit of the interrupt that occurs only when L1-ICache1 preload-operation is done."]
pub type L1_ICACHE1_PLD_DONE_INT_RAW_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `L1_ICACHE2_PLD_DONE_INT_RAW` reader - Reserved"]
pub type L1_ICACHE2_PLD_DONE_INT_RAW_R = crate::BitReader;
#[doc = "Field `L1_ICACHE2_PLD_DONE_INT_RAW` writer - Reserved"]
pub type L1_ICACHE2_PLD_DONE_INT_RAW_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `L1_ICACHE3_PLD_DONE_INT_RAW` reader - Reserved"]
pub type L1_ICACHE3_PLD_DONE_INT_RAW_R = crate::BitReader;
#[doc = "Field `L1_ICACHE3_PLD_DONE_INT_RAW` writer - Reserved"]
pub type L1_ICACHE3_PLD_DONE_INT_RAW_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `L1_CACHE_PLD_DONE_INT_RAW` reader - The raw bit of the interrupt that occurs only when L1-Cache preload-operation is done."]
pub type L1_CACHE_PLD_DONE_INT_RAW_R = crate::BitReader;
#[doc = "Field `L1_CACHE_PLD_DONE_INT_RAW` writer - The raw bit of the interrupt that occurs only when L1-Cache preload-operation is done."]
pub type L1_CACHE_PLD_DONE_INT_RAW_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CACHE_SYNC_DONE_INT_RAW` reader - The raw bit of the interrupt that occurs only when Cache sync-operation is done."]
pub type CACHE_SYNC_DONE_INT_RAW_R = crate::BitReader;
#[doc = "Field `CACHE_SYNC_DONE_INT_RAW` writer - The raw bit of the interrupt that occurs only when Cache sync-operation is done."]
pub type CACHE_SYNC_DONE_INT_RAW_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `L1_ICACHE0_PLD_ERR_INT_RAW` reader - The raw bit of the interrupt that occurs only when L1-ICache0 preload-operation error occurs."]
pub type L1_ICACHE0_PLD_ERR_INT_RAW_R = crate::BitReader;
#[doc = "Field `L1_ICACHE0_PLD_ERR_INT_RAW` writer - The raw bit of the interrupt that occurs only when L1-ICache0 preload-operation error occurs."]
pub type L1_ICACHE0_PLD_ERR_INT_RAW_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `L1_ICACHE1_PLD_ERR_INT_RAW` reader - The raw bit of the interrupt that occurs only when L1-ICache1 preload-operation error occurs."]
pub type L1_ICACHE1_PLD_ERR_INT_RAW_R = crate::BitReader;
#[doc = "Field `L1_ICACHE1_PLD_ERR_INT_RAW` writer - The raw bit of the interrupt that occurs only when L1-ICache1 preload-operation error occurs."]
pub type L1_ICACHE1_PLD_ERR_INT_RAW_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `L1_ICACHE2_PLD_ERR_INT_RAW` reader - Reserved"]
pub type L1_ICACHE2_PLD_ERR_INT_RAW_R = crate::BitReader;
#[doc = "Field `L1_ICACHE2_PLD_ERR_INT_RAW` writer - Reserved"]
pub type L1_ICACHE2_PLD_ERR_INT_RAW_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `L1_ICACHE3_PLD_ERR_INT_RAW` reader - Reserved"]
pub type L1_ICACHE3_PLD_ERR_INT_RAW_R = crate::BitReader;
#[doc = "Field `L1_ICACHE3_PLD_ERR_INT_RAW` writer - Reserved"]
pub type L1_ICACHE3_PLD_ERR_INT_RAW_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `L1_CACHE_PLD_ERR_INT_RAW` reader - The raw bit of the interrupt that occurs only when L1-Cache preload-operation error occurs."]
pub type L1_CACHE_PLD_ERR_INT_RAW_R = crate::BitReader;
#[doc = "Field `L1_CACHE_PLD_ERR_INT_RAW` writer - The raw bit of the interrupt that occurs only when L1-Cache preload-operation error occurs."]
pub type L1_CACHE_PLD_ERR_INT_RAW_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CACHE_SYNC_ERR_INT_RAW` reader - The raw bit of the interrupt that occurs only when Cache sync-operation error occurs."]
pub type CACHE_SYNC_ERR_INT_RAW_R = crate::BitReader;
#[doc = "Field `CACHE_SYNC_ERR_INT_RAW` writer - The raw bit of the interrupt that occurs only when Cache sync-operation error occurs."]
pub type CACHE_SYNC_ERR_INT_RAW_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - The raw bit of the interrupt that occurs only when L1-ICache0 preload-operation is done."]
    #[inline(always)]
    pub fn l1_icache0_pld_done_int_raw(&self) -> L1_ICACHE0_PLD_DONE_INT_RAW_R {
        L1_ICACHE0_PLD_DONE_INT_RAW_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The raw bit of the interrupt that occurs only when L1-ICache1 preload-operation is done."]
    #[inline(always)]
    pub fn l1_icache1_pld_done_int_raw(&self) -> L1_ICACHE1_PLD_DONE_INT_RAW_R {
        L1_ICACHE1_PLD_DONE_INT_RAW_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Reserved"]
    #[inline(always)]
    pub fn l1_icache2_pld_done_int_raw(&self) -> L1_ICACHE2_PLD_DONE_INT_RAW_R {
        L1_ICACHE2_PLD_DONE_INT_RAW_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Reserved"]
    #[inline(always)]
    pub fn l1_icache3_pld_done_int_raw(&self) -> L1_ICACHE3_PLD_DONE_INT_RAW_R {
        L1_ICACHE3_PLD_DONE_INT_RAW_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - The raw bit of the interrupt that occurs only when L1-Cache preload-operation is done."]
    #[inline(always)]
    pub fn l1_cache_pld_done_int_raw(&self) -> L1_CACHE_PLD_DONE_INT_RAW_R {
        L1_CACHE_PLD_DONE_INT_RAW_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 6 - The raw bit of the interrupt that occurs only when Cache sync-operation is done."]
    #[inline(always)]
    pub fn cache_sync_done_int_raw(&self) -> CACHE_SYNC_DONE_INT_RAW_R {
        CACHE_SYNC_DONE_INT_RAW_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - The raw bit of the interrupt that occurs only when L1-ICache0 preload-operation error occurs."]
    #[inline(always)]
    pub fn l1_icache0_pld_err_int_raw(&self) -> L1_ICACHE0_PLD_ERR_INT_RAW_R {
        L1_ICACHE0_PLD_ERR_INT_RAW_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - The raw bit of the interrupt that occurs only when L1-ICache1 preload-operation error occurs."]
    #[inline(always)]
    pub fn l1_icache1_pld_err_int_raw(&self) -> L1_ICACHE1_PLD_ERR_INT_RAW_R {
        L1_ICACHE1_PLD_ERR_INT_RAW_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Reserved"]
    #[inline(always)]
    pub fn l1_icache2_pld_err_int_raw(&self) -> L1_ICACHE2_PLD_ERR_INT_RAW_R {
        L1_ICACHE2_PLD_ERR_INT_RAW_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Reserved"]
    #[inline(always)]
    pub fn l1_icache3_pld_err_int_raw(&self) -> L1_ICACHE3_PLD_ERR_INT_RAW_R {
        L1_ICACHE3_PLD_ERR_INT_RAW_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - The raw bit of the interrupt that occurs only when L1-Cache preload-operation error occurs."]
    #[inline(always)]
    pub fn l1_cache_pld_err_int_raw(&self) -> L1_CACHE_PLD_ERR_INT_RAW_R {
        L1_CACHE_PLD_ERR_INT_RAW_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 13 - The raw bit of the interrupt that occurs only when Cache sync-operation error occurs."]
    #[inline(always)]
    pub fn cache_sync_err_int_raw(&self) -> CACHE_SYNC_ERR_INT_RAW_R {
        CACHE_SYNC_ERR_INT_RAW_R::new(((self.bits >> 13) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L1_CACHE_SYNC_PRELOAD_INT_RAW")
            .field(
                "l1_icache0_pld_done_int_raw",
                &self.l1_icache0_pld_done_int_raw(),
            )
            .field(
                "l1_icache1_pld_done_int_raw",
                &self.l1_icache1_pld_done_int_raw(),
            )
            .field(
                "l1_icache2_pld_done_int_raw",
                &self.l1_icache2_pld_done_int_raw(),
            )
            .field(
                "l1_icache3_pld_done_int_raw",
                &self.l1_icache3_pld_done_int_raw(),
            )
            .field(
                "l1_cache_pld_done_int_raw",
                &self.l1_cache_pld_done_int_raw(),
            )
            .field("cache_sync_done_int_raw", &self.cache_sync_done_int_raw())
            .field(
                "l1_icache0_pld_err_int_raw",
                &self.l1_icache0_pld_err_int_raw(),
            )
            .field(
                "l1_icache1_pld_err_int_raw",
                &self.l1_icache1_pld_err_int_raw(),
            )
            .field(
                "l1_icache2_pld_err_int_raw",
                &self.l1_icache2_pld_err_int_raw(),
            )
            .field(
                "l1_icache3_pld_err_int_raw",
                &self.l1_icache3_pld_err_int_raw(),
            )
            .field("l1_cache_pld_err_int_raw", &self.l1_cache_pld_err_int_raw())
            .field("cache_sync_err_int_raw", &self.cache_sync_err_int_raw())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - The raw bit of the interrupt that occurs only when L1-ICache0 preload-operation is done."]
    #[inline(always)]
    pub fn l1_icache0_pld_done_int_raw(
        &mut self,
    ) -> L1_ICACHE0_PLD_DONE_INT_RAW_W<'_, L1_CACHE_SYNC_PRELOAD_INT_RAW_SPEC> {
        L1_ICACHE0_PLD_DONE_INT_RAW_W::new(self, 0)
    }
    #[doc = "Bit 1 - The raw bit of the interrupt that occurs only when L1-ICache1 preload-operation is done."]
    #[inline(always)]
    pub fn l1_icache1_pld_done_int_raw(
        &mut self,
    ) -> L1_ICACHE1_PLD_DONE_INT_RAW_W<'_, L1_CACHE_SYNC_PRELOAD_INT_RAW_SPEC> {
        L1_ICACHE1_PLD_DONE_INT_RAW_W::new(self, 1)
    }
    #[doc = "Bit 2 - Reserved"]
    #[inline(always)]
    pub fn l1_icache2_pld_done_int_raw(
        &mut self,
    ) -> L1_ICACHE2_PLD_DONE_INT_RAW_W<'_, L1_CACHE_SYNC_PRELOAD_INT_RAW_SPEC> {
        L1_ICACHE2_PLD_DONE_INT_RAW_W::new(self, 2)
    }
    #[doc = "Bit 3 - Reserved"]
    #[inline(always)]
    pub fn l1_icache3_pld_done_int_raw(
        &mut self,
    ) -> L1_ICACHE3_PLD_DONE_INT_RAW_W<'_, L1_CACHE_SYNC_PRELOAD_INT_RAW_SPEC> {
        L1_ICACHE3_PLD_DONE_INT_RAW_W::new(self, 3)
    }
    #[doc = "Bit 4 - The raw bit of the interrupt that occurs only when L1-Cache preload-operation is done."]
    #[inline(always)]
    pub fn l1_cache_pld_done_int_raw(
        &mut self,
    ) -> L1_CACHE_PLD_DONE_INT_RAW_W<'_, L1_CACHE_SYNC_PRELOAD_INT_RAW_SPEC> {
        L1_CACHE_PLD_DONE_INT_RAW_W::new(self, 4)
    }
    #[doc = "Bit 6 - The raw bit of the interrupt that occurs only when Cache sync-operation is done."]
    #[inline(always)]
    pub fn cache_sync_done_int_raw(
        &mut self,
    ) -> CACHE_SYNC_DONE_INT_RAW_W<'_, L1_CACHE_SYNC_PRELOAD_INT_RAW_SPEC> {
        CACHE_SYNC_DONE_INT_RAW_W::new(self, 6)
    }
    #[doc = "Bit 7 - The raw bit of the interrupt that occurs only when L1-ICache0 preload-operation error occurs."]
    #[inline(always)]
    pub fn l1_icache0_pld_err_int_raw(
        &mut self,
    ) -> L1_ICACHE0_PLD_ERR_INT_RAW_W<'_, L1_CACHE_SYNC_PRELOAD_INT_RAW_SPEC> {
        L1_ICACHE0_PLD_ERR_INT_RAW_W::new(self, 7)
    }
    #[doc = "Bit 8 - The raw bit of the interrupt that occurs only when L1-ICache1 preload-operation error occurs."]
    #[inline(always)]
    pub fn l1_icache1_pld_err_int_raw(
        &mut self,
    ) -> L1_ICACHE1_PLD_ERR_INT_RAW_W<'_, L1_CACHE_SYNC_PRELOAD_INT_RAW_SPEC> {
        L1_ICACHE1_PLD_ERR_INT_RAW_W::new(self, 8)
    }
    #[doc = "Bit 9 - Reserved"]
    #[inline(always)]
    pub fn l1_icache2_pld_err_int_raw(
        &mut self,
    ) -> L1_ICACHE2_PLD_ERR_INT_RAW_W<'_, L1_CACHE_SYNC_PRELOAD_INT_RAW_SPEC> {
        L1_ICACHE2_PLD_ERR_INT_RAW_W::new(self, 9)
    }
    #[doc = "Bit 10 - Reserved"]
    #[inline(always)]
    pub fn l1_icache3_pld_err_int_raw(
        &mut self,
    ) -> L1_ICACHE3_PLD_ERR_INT_RAW_W<'_, L1_CACHE_SYNC_PRELOAD_INT_RAW_SPEC> {
        L1_ICACHE3_PLD_ERR_INT_RAW_W::new(self, 10)
    }
    #[doc = "Bit 11 - The raw bit of the interrupt that occurs only when L1-Cache preload-operation error occurs."]
    #[inline(always)]
    pub fn l1_cache_pld_err_int_raw(
        &mut self,
    ) -> L1_CACHE_PLD_ERR_INT_RAW_W<'_, L1_CACHE_SYNC_PRELOAD_INT_RAW_SPEC> {
        L1_CACHE_PLD_ERR_INT_RAW_W::new(self, 11)
    }
    #[doc = "Bit 13 - The raw bit of the interrupt that occurs only when Cache sync-operation error occurs."]
    #[inline(always)]
    pub fn cache_sync_err_int_raw(
        &mut self,
    ) -> CACHE_SYNC_ERR_INT_RAW_W<'_, L1_CACHE_SYNC_PRELOAD_INT_RAW_SPEC> {
        CACHE_SYNC_ERR_INT_RAW_W::new(self, 13)
    }
}
#[doc = "Sync Preload operation Interrupt raw register\n\nYou can [`read`](crate::Reg::read) this register and get [`l1_cache_sync_preload_int_raw::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`l1_cache_sync_preload_int_raw::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L1_CACHE_SYNC_PRELOAD_INT_RAW_SPEC;
impl crate::RegisterSpec for L1_CACHE_SYNC_PRELOAD_INT_RAW_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l1_cache_sync_preload_int_raw::R`](R) reader structure"]
impl crate::Readable for L1_CACHE_SYNC_PRELOAD_INT_RAW_SPEC {}
#[doc = "`write(|w| ..)` method takes [`l1_cache_sync_preload_int_raw::W`](W) writer structure"]
impl crate::Writable for L1_CACHE_SYNC_PRELOAD_INT_RAW_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets L1_CACHE_SYNC_PRELOAD_INT_RAW to value 0"]
impl crate::Resettable for L1_CACHE_SYNC_PRELOAD_INT_RAW_SPEC {}
