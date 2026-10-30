#[doc = "Register `L1_CACHE_SYNC_PRELOAD_EXCEPTION` reader"]
pub type R = crate::R<L1_CACHE_SYNC_PRELOAD_EXCEPTION_SPEC>;
#[doc = "Field `L1_ICACHE0_PLD_ERR_CODE` reader - The value 2 is Only available which means preload size is error in L1-ICache0."]
pub type L1_ICACHE0_PLD_ERR_CODE_R = crate::FieldReader;
#[doc = "Field `L1_ICACHE1_PLD_ERR_CODE` reader - The value 2 is Only available which means preload size is error in L1-ICache1."]
pub type L1_ICACHE1_PLD_ERR_CODE_R = crate::FieldReader;
#[doc = "Field `L1_ICACHE2_PLD_ERR_CODE` reader - Reserved"]
pub type L1_ICACHE2_PLD_ERR_CODE_R = crate::FieldReader;
#[doc = "Field `L1_ICACHE3_PLD_ERR_CODE` reader - Reserved"]
pub type L1_ICACHE3_PLD_ERR_CODE_R = crate::FieldReader;
#[doc = "Field `L1_CACHE_PLD_ERR_CODE` reader - The value 2 is Only available which means preload size is error in L1-Cache."]
pub type L1_CACHE_PLD_ERR_CODE_R = crate::FieldReader;
#[doc = "Field `CACHE_SYNC_ERR_CODE` reader - The values 0-2 are available which means sync map, command conflict and size are error in Cache System."]
pub type CACHE_SYNC_ERR_CODE_R = crate::FieldReader;
impl R {
    #[doc = "Bits 0:1 - The value 2 is Only available which means preload size is error in L1-ICache0."]
    #[inline(always)]
    pub fn l1_icache0_pld_err_code(&self) -> L1_ICACHE0_PLD_ERR_CODE_R {
        L1_ICACHE0_PLD_ERR_CODE_R::new((self.bits & 3) as u8)
    }
    #[doc = "Bits 2:3 - The value 2 is Only available which means preload size is error in L1-ICache1."]
    #[inline(always)]
    pub fn l1_icache1_pld_err_code(&self) -> L1_ICACHE1_PLD_ERR_CODE_R {
        L1_ICACHE1_PLD_ERR_CODE_R::new(((self.bits >> 2) & 3) as u8)
    }
    #[doc = "Bits 4:5 - Reserved"]
    #[inline(always)]
    pub fn l1_icache2_pld_err_code(&self) -> L1_ICACHE2_PLD_ERR_CODE_R {
        L1_ICACHE2_PLD_ERR_CODE_R::new(((self.bits >> 4) & 3) as u8)
    }
    #[doc = "Bits 6:7 - Reserved"]
    #[inline(always)]
    pub fn l1_icache3_pld_err_code(&self) -> L1_ICACHE3_PLD_ERR_CODE_R {
        L1_ICACHE3_PLD_ERR_CODE_R::new(((self.bits >> 6) & 3) as u8)
    }
    #[doc = "Bits 8:9 - The value 2 is Only available which means preload size is error in L1-Cache."]
    #[inline(always)]
    pub fn l1_cache_pld_err_code(&self) -> L1_CACHE_PLD_ERR_CODE_R {
        L1_CACHE_PLD_ERR_CODE_R::new(((self.bits >> 8) & 3) as u8)
    }
    #[doc = "Bits 12:13 - The values 0-2 are available which means sync map, command conflict and size are error in Cache System."]
    #[inline(always)]
    pub fn cache_sync_err_code(&self) -> CACHE_SYNC_ERR_CODE_R {
        CACHE_SYNC_ERR_CODE_R::new(((self.bits >> 12) & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L1_CACHE_SYNC_PRELOAD_EXCEPTION")
            .field("l1_icache0_pld_err_code", &self.l1_icache0_pld_err_code())
            .field("l1_icache1_pld_err_code", &self.l1_icache1_pld_err_code())
            .field("l1_icache2_pld_err_code", &self.l1_icache2_pld_err_code())
            .field("l1_icache3_pld_err_code", &self.l1_icache3_pld_err_code())
            .field("l1_cache_pld_err_code", &self.l1_cache_pld_err_code())
            .field("cache_sync_err_code", &self.cache_sync_err_code())
            .finish()
    }
}
#[doc = "Cache Sync/Preload Operation exception register\n\nYou can [`read`](crate::Reg::read) this register and get [`l1_cache_sync_preload_exception::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L1_CACHE_SYNC_PRELOAD_EXCEPTION_SPEC;
impl crate::RegisterSpec for L1_CACHE_SYNC_PRELOAD_EXCEPTION_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l1_cache_sync_preload_exception::R`](R) reader structure"]
impl crate::Readable for L1_CACHE_SYNC_PRELOAD_EXCEPTION_SPEC {}
#[doc = "`reset()` method sets L1_CACHE_SYNC_PRELOAD_EXCEPTION to value 0"]
impl crate::Resettable for L1_CACHE_SYNC_PRELOAD_EXCEPTION_SPEC {}
