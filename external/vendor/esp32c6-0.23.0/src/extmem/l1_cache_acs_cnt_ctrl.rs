#[doc = "Register `L1_CACHE_ACS_CNT_CTRL` reader"]
pub type R = crate::R<L1_CACHE_ACS_CNT_CTRL_SPEC>;
#[doc = "Register `L1_CACHE_ACS_CNT_CTRL` writer"]
pub type W = crate::W<L1_CACHE_ACS_CNT_CTRL_SPEC>;
#[doc = "Field `L1_IBUS0_CNT_ENA` reader - The bit is used to enable ibus0 counter in L1-ICache0."]
pub type L1_IBUS0_CNT_ENA_R = crate::BitReader;
#[doc = "Field `L1_IBUS1_CNT_ENA` reader - The bit is used to enable ibus1 counter in L1-ICache1."]
pub type L1_IBUS1_CNT_ENA_R = crate::BitReader;
#[doc = "Field `L1_IBUS2_CNT_ENA` reader - Reserved"]
pub type L1_IBUS2_CNT_ENA_R = crate::BitReader;
#[doc = "Field `L1_IBUS3_CNT_ENA` reader - Reserved"]
pub type L1_IBUS3_CNT_ENA_R = crate::BitReader;
#[doc = "Field `L1_BUS0_CNT_ENA` reader - The bit is used to enable dbus0 counter in L1-DCache."]
pub type L1_BUS0_CNT_ENA_R = crate::BitReader;
#[doc = "Field `L1_BUS0_CNT_ENA` writer - The bit is used to enable dbus0 counter in L1-DCache."]
pub type L1_BUS0_CNT_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `L1_BUS1_CNT_ENA` reader - The bit is used to enable dbus1 counter in L1-DCache."]
pub type L1_BUS1_CNT_ENA_R = crate::BitReader;
#[doc = "Field `L1_BUS1_CNT_ENA` writer - The bit is used to enable dbus1 counter in L1-DCache."]
pub type L1_BUS1_CNT_ENA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `L1_DBUS2_CNT_ENA` reader - Reserved"]
pub type L1_DBUS2_CNT_ENA_R = crate::BitReader;
#[doc = "Field `L1_DBUS3_CNT_ENA` reader - Reserved"]
pub type L1_DBUS3_CNT_ENA_R = crate::BitReader;
#[doc = "Field `L1_IBUS0_CNT_CLR` reader - The bit is used to clear ibus0 counter in L1-ICache0."]
pub type L1_IBUS0_CNT_CLR_R = crate::BitReader;
#[doc = "Field `L1_IBUS1_CNT_CLR` reader - The bit is used to clear ibus1 counter in L1-ICache1."]
pub type L1_IBUS1_CNT_CLR_R = crate::BitReader;
#[doc = "Field `L1_IBUS2_CNT_CLR` reader - Reserved"]
pub type L1_IBUS2_CNT_CLR_R = crate::BitReader;
#[doc = "Field `L1_IBUS3_CNT_CLR` reader - Reserved"]
pub type L1_IBUS3_CNT_CLR_R = crate::BitReader;
#[doc = "Field `L1_BUS0_CNT_CLR` writer - The bit is used to clear dbus0 counter in L1-DCache."]
pub type L1_BUS0_CNT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `L1_BUS1_CNT_CLR` writer - The bit is used to clear dbus1 counter in L1-DCache."]
pub type L1_BUS1_CNT_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `L1_DBUS2_CNT_CLR` reader - Reserved"]
pub type L1_DBUS2_CNT_CLR_R = crate::BitReader;
#[doc = "Field `L1_DBUS3_CNT_CLR` reader - Reserved"]
pub type L1_DBUS3_CNT_CLR_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - The bit is used to enable ibus0 counter in L1-ICache0."]
    #[inline(always)]
    pub fn l1_ibus0_cnt_ena(&self) -> L1_IBUS0_CNT_ENA_R {
        L1_IBUS0_CNT_ENA_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The bit is used to enable ibus1 counter in L1-ICache1."]
    #[inline(always)]
    pub fn l1_ibus1_cnt_ena(&self) -> L1_IBUS1_CNT_ENA_R {
        L1_IBUS1_CNT_ENA_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Reserved"]
    #[inline(always)]
    pub fn l1_ibus2_cnt_ena(&self) -> L1_IBUS2_CNT_ENA_R {
        L1_IBUS2_CNT_ENA_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Reserved"]
    #[inline(always)]
    pub fn l1_ibus3_cnt_ena(&self) -> L1_IBUS3_CNT_ENA_R {
        L1_IBUS3_CNT_ENA_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - The bit is used to enable dbus0 counter in L1-DCache."]
    #[inline(always)]
    pub fn l1_bus0_cnt_ena(&self) -> L1_BUS0_CNT_ENA_R {
        L1_BUS0_CNT_ENA_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - The bit is used to enable dbus1 counter in L1-DCache."]
    #[inline(always)]
    pub fn l1_bus1_cnt_ena(&self) -> L1_BUS1_CNT_ENA_R {
        L1_BUS1_CNT_ENA_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Reserved"]
    #[inline(always)]
    pub fn l1_dbus2_cnt_ena(&self) -> L1_DBUS2_CNT_ENA_R {
        L1_DBUS2_CNT_ENA_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Reserved"]
    #[inline(always)]
    pub fn l1_dbus3_cnt_ena(&self) -> L1_DBUS3_CNT_ENA_R {
        L1_DBUS3_CNT_ENA_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 16 - The bit is used to clear ibus0 counter in L1-ICache0."]
    #[inline(always)]
    pub fn l1_ibus0_cnt_clr(&self) -> L1_IBUS0_CNT_CLR_R {
        L1_IBUS0_CNT_CLR_R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - The bit is used to clear ibus1 counter in L1-ICache1."]
    #[inline(always)]
    pub fn l1_ibus1_cnt_clr(&self) -> L1_IBUS1_CNT_CLR_R {
        L1_IBUS1_CNT_CLR_R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - Reserved"]
    #[inline(always)]
    pub fn l1_ibus2_cnt_clr(&self) -> L1_IBUS2_CNT_CLR_R {
        L1_IBUS2_CNT_CLR_R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - Reserved"]
    #[inline(always)]
    pub fn l1_ibus3_cnt_clr(&self) -> L1_IBUS3_CNT_CLR_R {
        L1_IBUS3_CNT_CLR_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 22 - Reserved"]
    #[inline(always)]
    pub fn l1_dbus2_cnt_clr(&self) -> L1_DBUS2_CNT_CLR_R {
        L1_DBUS2_CNT_CLR_R::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 23 - Reserved"]
    #[inline(always)]
    pub fn l1_dbus3_cnt_clr(&self) -> L1_DBUS3_CNT_CLR_R {
        L1_DBUS3_CNT_CLR_R::new(((self.bits >> 23) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L1_CACHE_ACS_CNT_CTRL")
            .field("l1_ibus0_cnt_ena", &self.l1_ibus0_cnt_ena())
            .field("l1_ibus1_cnt_ena", &self.l1_ibus1_cnt_ena())
            .field("l1_ibus2_cnt_ena", &self.l1_ibus2_cnt_ena())
            .field("l1_ibus3_cnt_ena", &self.l1_ibus3_cnt_ena())
            .field("l1_bus0_cnt_ena", &self.l1_bus0_cnt_ena())
            .field("l1_bus1_cnt_ena", &self.l1_bus1_cnt_ena())
            .field("l1_dbus2_cnt_ena", &self.l1_dbus2_cnt_ena())
            .field("l1_dbus3_cnt_ena", &self.l1_dbus3_cnt_ena())
            .field("l1_ibus0_cnt_clr", &self.l1_ibus0_cnt_clr())
            .field("l1_ibus1_cnt_clr", &self.l1_ibus1_cnt_clr())
            .field("l1_ibus2_cnt_clr", &self.l1_ibus2_cnt_clr())
            .field("l1_ibus3_cnt_clr", &self.l1_ibus3_cnt_clr())
            .field("l1_dbus2_cnt_clr", &self.l1_dbus2_cnt_clr())
            .field("l1_dbus3_cnt_clr", &self.l1_dbus3_cnt_clr())
            .finish()
    }
}
impl W {
    #[doc = "Bit 4 - The bit is used to enable dbus0 counter in L1-DCache."]
    #[inline(always)]
    pub fn l1_bus0_cnt_ena(&mut self) -> L1_BUS0_CNT_ENA_W<'_, L1_CACHE_ACS_CNT_CTRL_SPEC> {
        L1_BUS0_CNT_ENA_W::new(self, 4)
    }
    #[doc = "Bit 5 - The bit is used to enable dbus1 counter in L1-DCache."]
    #[inline(always)]
    pub fn l1_bus1_cnt_ena(&mut self) -> L1_BUS1_CNT_ENA_W<'_, L1_CACHE_ACS_CNT_CTRL_SPEC> {
        L1_BUS1_CNT_ENA_W::new(self, 5)
    }
    #[doc = "Bit 20 - The bit is used to clear dbus0 counter in L1-DCache."]
    #[inline(always)]
    pub fn l1_bus0_cnt_clr(&mut self) -> L1_BUS0_CNT_CLR_W<'_, L1_CACHE_ACS_CNT_CTRL_SPEC> {
        L1_BUS0_CNT_CLR_W::new(self, 20)
    }
    #[doc = "Bit 21 - The bit is used to clear dbus1 counter in L1-DCache."]
    #[inline(always)]
    pub fn l1_bus1_cnt_clr(&mut self) -> L1_BUS1_CNT_CLR_W<'_, L1_CACHE_ACS_CNT_CTRL_SPEC> {
        L1_BUS1_CNT_CLR_W::new(self, 21)
    }
}
#[doc = "Cache Access Counter enable and clear register\n\nYou can [`read`](crate::Reg::read) this register and get [`l1_cache_acs_cnt_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`l1_cache_acs_cnt_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L1_CACHE_ACS_CNT_CTRL_SPEC;
impl crate::RegisterSpec for L1_CACHE_ACS_CNT_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l1_cache_acs_cnt_ctrl::R`](R) reader structure"]
impl crate::Readable for L1_CACHE_ACS_CNT_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`l1_cache_acs_cnt_ctrl::W`](W) writer structure"]
impl crate::Writable for L1_CACHE_ACS_CNT_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets L1_CACHE_ACS_CNT_CTRL to value 0"]
impl crate::Resettable for L1_CACHE_ACS_CNT_CTRL_SPEC {}
