#[doc = "Register `CACHE_ILG_INT_CLR` writer"]
pub type W = crate::W<CACHE_ILG_INT_CLR_SPEC>;
#[doc = "Field `ICACHE_SYNC_OP_FAULT` writer - The bit is used to clear interrupt by sync configurations fault."]
pub type ICACHE_SYNC_OP_FAULT_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `ICACHE_PRELOAD_OP_FAULT` writer - The bit is used to clear interrupt by preload configurations fault."]
pub type ICACHE_PRELOAD_OP_FAULT_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `MMU_ENTRY_FAULT` writer - The bit is used to clear interrupt by mmu entry fault."]
pub type MMU_ENTRY_FAULT_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `IBUS_CNT_OVF` writer - The bit is used to clear interrupt by ibus counter overflow."]
pub type IBUS_CNT_OVF_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `DBUS_CNT_OVF` writer - The bit is used to clear interrupt by dbus counter overflow."]
pub type DBUS_CNT_OVF_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<CACHE_ILG_INT_CLR_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - The bit is used to clear interrupt by sync configurations fault."]
    #[inline(always)]
    pub fn icache_sync_op_fault(&mut self) -> ICACHE_SYNC_OP_FAULT_W<'_, CACHE_ILG_INT_CLR_SPEC> {
        ICACHE_SYNC_OP_FAULT_W::new(self, 0)
    }
    #[doc = "Bit 1 - The bit is used to clear interrupt by preload configurations fault."]
    #[inline(always)]
    pub fn icache_preload_op_fault(
        &mut self,
    ) -> ICACHE_PRELOAD_OP_FAULT_W<'_, CACHE_ILG_INT_CLR_SPEC> {
        ICACHE_PRELOAD_OP_FAULT_W::new(self, 1)
    }
    #[doc = "Bit 5 - The bit is used to clear interrupt by mmu entry fault."]
    #[inline(always)]
    pub fn mmu_entry_fault(&mut self) -> MMU_ENTRY_FAULT_W<'_, CACHE_ILG_INT_CLR_SPEC> {
        MMU_ENTRY_FAULT_W::new(self, 5)
    }
    #[doc = "Bit 7 - The bit is used to clear interrupt by ibus counter overflow."]
    #[inline(always)]
    pub fn ibus_cnt_ovf(&mut self) -> IBUS_CNT_OVF_W<'_, CACHE_ILG_INT_CLR_SPEC> {
        IBUS_CNT_OVF_W::new(self, 7)
    }
    #[doc = "Bit 8 - The bit is used to clear interrupt by dbus counter overflow."]
    #[inline(always)]
    pub fn dbus_cnt_ovf(&mut self) -> DBUS_CNT_OVF_W<'_, CACHE_ILG_INT_CLR_SPEC> {
        DBUS_CNT_OVF_W::new(self, 8)
    }
}
#[doc = "This description will be updated in the near future.\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cache_ilg_int_clr::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CACHE_ILG_INT_CLR_SPEC;
impl crate::RegisterSpec for CACHE_ILG_INT_CLR_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`cache_ilg_int_clr::W`](W) writer structure"]
impl crate::Writable for CACHE_ILG_INT_CLR_SPEC {
    type Safety = crate::Unsafe;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0x01a3;
}
#[doc = "`reset()` method sets CACHE_ILG_INT_CLR to value 0"]
impl crate::Resettable for CACHE_ILG_INT_CLR_SPEC {}
