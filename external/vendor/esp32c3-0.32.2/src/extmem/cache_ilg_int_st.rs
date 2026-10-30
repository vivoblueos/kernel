#[doc = "Register `CACHE_ILG_INT_ST` reader"]
pub type R = crate::R<CACHE_ILG_INT_ST_SPEC>;
#[doc = "Field `ICACHE_SYNC_OP_FAULT` reader - The bit is used to indicate interrupt by sync configurations fault."]
pub type ICACHE_SYNC_OP_FAULT_R = crate::BitReader;
#[doc = "Field `ICACHE_PRELOAD_OP_FAULT` reader - The bit is used to indicate interrupt by preload configurations fault."]
pub type ICACHE_PRELOAD_OP_FAULT_R = crate::BitReader;
#[doc = "Field `MMU_ENTRY_FAULT` reader - The bit is used to indicate interrupt by mmu entry fault."]
pub type MMU_ENTRY_FAULT_R = crate::BitReader;
#[doc = "Field `IBUS_ACS_CNT_OVF` reader - The bit is used to indicate interrupt by ibus access flash/spiram counter overflow."]
pub type IBUS_ACS_CNT_OVF_R = crate::BitReader;
#[doc = "Field `IBUS_ACS_MISS_CNT_OVF` reader - The bit is used to indicate interrupt by ibus access flash/spiram miss counter overflow."]
pub type IBUS_ACS_MISS_CNT_OVF_R = crate::BitReader;
#[doc = "Field `DBUS_ACS_CNT_OVF` reader - The bit is used to indicate interrupt by dbus access flash/spiram counter overflow."]
pub type DBUS_ACS_CNT_OVF_R = crate::BitReader;
#[doc = "Field `DBUS_ACS_FLASH_MISS_CNT_OVF` reader - The bit is used to indicate interrupt by dbus access flash miss counter overflow."]
pub type DBUS_ACS_FLASH_MISS_CNT_OVF_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - The bit is used to indicate interrupt by sync configurations fault."]
    #[inline(always)]
    pub fn icache_sync_op_fault(&self) -> ICACHE_SYNC_OP_FAULT_R {
        ICACHE_SYNC_OP_FAULT_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The bit is used to indicate interrupt by preload configurations fault."]
    #[inline(always)]
    pub fn icache_preload_op_fault(&self) -> ICACHE_PRELOAD_OP_FAULT_R {
        ICACHE_PRELOAD_OP_FAULT_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 5 - The bit is used to indicate interrupt by mmu entry fault."]
    #[inline(always)]
    pub fn mmu_entry_fault(&self) -> MMU_ENTRY_FAULT_R {
        MMU_ENTRY_FAULT_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 7 - The bit is used to indicate interrupt by ibus access flash/spiram counter overflow."]
    #[inline(always)]
    pub fn ibus_acs_cnt_ovf(&self) -> IBUS_ACS_CNT_OVF_R {
        IBUS_ACS_CNT_OVF_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - The bit is used to indicate interrupt by ibus access flash/spiram miss counter overflow."]
    #[inline(always)]
    pub fn ibus_acs_miss_cnt_ovf(&self) -> IBUS_ACS_MISS_CNT_OVF_R {
        IBUS_ACS_MISS_CNT_OVF_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - The bit is used to indicate interrupt by dbus access flash/spiram counter overflow."]
    #[inline(always)]
    pub fn dbus_acs_cnt_ovf(&self) -> DBUS_ACS_CNT_OVF_R {
        DBUS_ACS_CNT_OVF_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - The bit is used to indicate interrupt by dbus access flash miss counter overflow."]
    #[inline(always)]
    pub fn dbus_acs_flash_miss_cnt_ovf(&self) -> DBUS_ACS_FLASH_MISS_CNT_OVF_R {
        DBUS_ACS_FLASH_MISS_CNT_OVF_R::new(((self.bits >> 10) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CACHE_ILG_INT_ST")
            .field("icache_sync_op_fault", &self.icache_sync_op_fault())
            .field("icache_preload_op_fault", &self.icache_preload_op_fault())
            .field("mmu_entry_fault", &self.mmu_entry_fault())
            .field("ibus_acs_cnt_ovf", &self.ibus_acs_cnt_ovf())
            .field("ibus_acs_miss_cnt_ovf", &self.ibus_acs_miss_cnt_ovf())
            .field("dbus_acs_cnt_ovf", &self.dbus_acs_cnt_ovf())
            .field(
                "dbus_acs_flash_miss_cnt_ovf",
                &self.dbus_acs_flash_miss_cnt_ovf(),
            )
            .finish()
    }
}
#[doc = "This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`cache_ilg_int_st::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CACHE_ILG_INT_ST_SPEC;
impl crate::RegisterSpec for CACHE_ILG_INT_ST_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cache_ilg_int_st::R`](R) reader structure"]
impl crate::Readable for CACHE_ILG_INT_ST_SPEC {}
#[doc = "`reset()` method sets CACHE_ILG_INT_ST to value 0"]
impl crate::Resettable for CACHE_ILG_INT_ST_SPEC {}
