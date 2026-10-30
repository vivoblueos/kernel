#[doc = "Register `L1_CACHE_ACS_CNT_INT_CLR` reader"]
pub type R = crate::R<L1_CACHE_ACS_CNT_INT_CLR_SPEC>;
#[doc = "Register `L1_CACHE_ACS_CNT_INT_CLR` writer"]
pub type W = crate::W<L1_CACHE_ACS_CNT_INT_CLR_SPEC>;
#[doc = "Field `L1_IBUS0_OVF_INT_CLR` reader - The bit is used to clear counters overflow interrupt and counters in L1-ICache0 due to bus0 accesses L1-ICache0."]
pub type L1_IBUS0_OVF_INT_CLR_R = crate::BitReader;
#[doc = "Field `L1_IBUS1_OVF_INT_CLR` reader - The bit is used to clear counters overflow interrupt and counters in L1-ICache1 due to bus1 accesses L1-ICache1."]
pub type L1_IBUS1_OVF_INT_CLR_R = crate::BitReader;
#[doc = "Field `L1_IBUS2_OVF_INT_CLR` reader - Reserved"]
pub type L1_IBUS2_OVF_INT_CLR_R = crate::BitReader;
#[doc = "Field `L1_IBUS3_OVF_INT_CLR` reader - Reserved"]
pub type L1_IBUS3_OVF_INT_CLR_R = crate::BitReader;
#[doc = "Field `L1_BUS0_OVF_INT_CLR` writer - The bit is used to clear counters overflow interrupt and counters in L1-DCache due to bus0 accesses L1-DCache."]
pub type L1_BUS0_OVF_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `L1_BUS1_OVF_INT_CLR` writer - The bit is used to clear counters overflow interrupt and counters in L1-DCache due to bus1 accesses L1-DCache."]
pub type L1_BUS1_OVF_INT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `L1_DBUS2_OVF_INT_CLR` reader - Reserved"]
pub type L1_DBUS2_OVF_INT_CLR_R = crate::BitReader;
#[doc = "Field `L1_DBUS3_OVF_INT_CLR` reader - Reserved"]
pub type L1_DBUS3_OVF_INT_CLR_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - The bit is used to clear counters overflow interrupt and counters in L1-ICache0 due to bus0 accesses L1-ICache0."]
    #[inline(always)]
    pub fn l1_ibus0_ovf_int_clr(&self) -> L1_IBUS0_OVF_INT_CLR_R {
        L1_IBUS0_OVF_INT_CLR_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The bit is used to clear counters overflow interrupt and counters in L1-ICache1 due to bus1 accesses L1-ICache1."]
    #[inline(always)]
    pub fn l1_ibus1_ovf_int_clr(&self) -> L1_IBUS1_OVF_INT_CLR_R {
        L1_IBUS1_OVF_INT_CLR_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Reserved"]
    #[inline(always)]
    pub fn l1_ibus2_ovf_int_clr(&self) -> L1_IBUS2_OVF_INT_CLR_R {
        L1_IBUS2_OVF_INT_CLR_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Reserved"]
    #[inline(always)]
    pub fn l1_ibus3_ovf_int_clr(&self) -> L1_IBUS3_OVF_INT_CLR_R {
        L1_IBUS3_OVF_INT_CLR_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 6 - Reserved"]
    #[inline(always)]
    pub fn l1_dbus2_ovf_int_clr(&self) -> L1_DBUS2_OVF_INT_CLR_R {
        L1_DBUS2_OVF_INT_CLR_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Reserved"]
    #[inline(always)]
    pub fn l1_dbus3_ovf_int_clr(&self) -> L1_DBUS3_OVF_INT_CLR_R {
        L1_DBUS3_OVF_INT_CLR_R::new(((self.bits >> 7) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L1_CACHE_ACS_CNT_INT_CLR")
            .field("l1_ibus0_ovf_int_clr", &self.l1_ibus0_ovf_int_clr())
            .field("l1_ibus1_ovf_int_clr", &self.l1_ibus1_ovf_int_clr())
            .field("l1_ibus2_ovf_int_clr", &self.l1_ibus2_ovf_int_clr())
            .field("l1_ibus3_ovf_int_clr", &self.l1_ibus3_ovf_int_clr())
            .field("l1_dbus2_ovf_int_clr", &self.l1_dbus2_ovf_int_clr())
            .field("l1_dbus3_ovf_int_clr", &self.l1_dbus3_ovf_int_clr())
            .finish()
    }
}
impl W {
    #[doc = "Bit 4 - The bit is used to clear counters overflow interrupt and counters in L1-DCache due to bus0 accesses L1-DCache."]
    #[inline(always)]
    pub fn l1_bus0_ovf_int_clr(
        &mut self,
    ) -> L1_BUS0_OVF_INT_CLR_W<'_, L1_CACHE_ACS_CNT_INT_CLR_SPEC> {
        L1_BUS0_OVF_INT_CLR_W::new(self, 4)
    }
    #[doc = "Bit 5 - The bit is used to clear counters overflow interrupt and counters in L1-DCache due to bus1 accesses L1-DCache."]
    #[inline(always)]
    pub fn l1_bus1_ovf_int_clr(
        &mut self,
    ) -> L1_BUS1_OVF_INT_CLR_W<'_, L1_CACHE_ACS_CNT_INT_CLR_SPEC> {
        L1_BUS1_OVF_INT_CLR_W::new(self, 5)
    }
}
#[doc = "Cache Access Counter Interrupt clear register\n\nYou can [`read`](crate::Reg::read) this register and get [`l1_cache_acs_cnt_int_clr::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`l1_cache_acs_cnt_int_clr::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L1_CACHE_ACS_CNT_INT_CLR_SPEC;
impl crate::RegisterSpec for L1_CACHE_ACS_CNT_INT_CLR_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l1_cache_acs_cnt_int_clr::R`](R) reader structure"]
impl crate::Readable for L1_CACHE_ACS_CNT_INT_CLR_SPEC {}
#[doc = "`write(|w| ..)` method takes [`l1_cache_acs_cnt_int_clr::W`](W) writer structure"]
impl crate::Writable for L1_CACHE_ACS_CNT_INT_CLR_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets L1_CACHE_ACS_CNT_INT_CLR to value 0"]
impl crate::Resettable for L1_CACHE_ACS_CNT_INT_CLR_SPEC {}
