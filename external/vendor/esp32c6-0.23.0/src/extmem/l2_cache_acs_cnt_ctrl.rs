#[doc = "Register `L2_CACHE_ACS_CNT_CTRL` reader"]
pub type R = crate::R<L2_CACHE_ACS_CNT_CTRL_SPEC>;
#[doc = "Field `L2_IBUS0_CNT_ENA` reader - The bit is used to enable ibus0 counter in L2-Cache."]
pub type L2_IBUS0_CNT_ENA_R = crate::BitReader;
#[doc = "Field `L2_IBUS1_CNT_ENA` reader - The bit is used to enable ibus1 counter in L2-Cache."]
pub type L2_IBUS1_CNT_ENA_R = crate::BitReader;
#[doc = "Field `L2_IBUS2_CNT_ENA` reader - Reserved"]
pub type L2_IBUS2_CNT_ENA_R = crate::BitReader;
#[doc = "Field `L2_IBUS3_CNT_ENA` reader - Reserved"]
pub type L2_IBUS3_CNT_ENA_R = crate::BitReader;
#[doc = "Field `L2_DBUS0_CNT_ENA` reader - The bit is used to enable dbus0 counter in L2-Cache."]
pub type L2_DBUS0_CNT_ENA_R = crate::BitReader;
#[doc = "Field `L2_DBUS1_CNT_ENA` reader - The bit is used to enable dbus1 counter in L2-Cache."]
pub type L2_DBUS1_CNT_ENA_R = crate::BitReader;
#[doc = "Field `L2_DBUS2_CNT_ENA` reader - Reserved"]
pub type L2_DBUS2_CNT_ENA_R = crate::BitReader;
#[doc = "Field `L2_DBUS3_CNT_ENA` reader - Reserved"]
pub type L2_DBUS3_CNT_ENA_R = crate::BitReader;
#[doc = "Field `L2_IBUS0_CNT_CLR` reader - The bit is used to clear ibus0 counter in L2-Cache."]
pub type L2_IBUS0_CNT_CLR_R = crate::BitReader;
#[doc = "Field `L2_IBUS1_CNT_CLR` reader - The bit is used to clear ibus1 counter in L2-Cache."]
pub type L2_IBUS1_CNT_CLR_R = crate::BitReader;
#[doc = "Field `L2_IBUS2_CNT_CLR` reader - Reserved"]
pub type L2_IBUS2_CNT_CLR_R = crate::BitReader;
#[doc = "Field `L2_IBUS3_CNT_CLR` reader - Reserved"]
pub type L2_IBUS3_CNT_CLR_R = crate::BitReader;
#[doc = "Field `L2_DBUS0_CNT_CLR` reader - The bit is used to clear dbus0 counter in L2-Cache."]
pub type L2_DBUS0_CNT_CLR_R = crate::BitReader;
#[doc = "Field `L2_DBUS1_CNT_CLR` reader - The bit is used to clear dbus1 counter in L2-Cache."]
pub type L2_DBUS1_CNT_CLR_R = crate::BitReader;
#[doc = "Field `L2_DBUS2_CNT_CLR` reader - Reserved"]
pub type L2_DBUS2_CNT_CLR_R = crate::BitReader;
#[doc = "Field `L2_DBUS3_CNT_CLR` reader - Reserved"]
pub type L2_DBUS3_CNT_CLR_R = crate::BitReader;
impl R {
    #[doc = "Bit 8 - The bit is used to enable ibus0 counter in L2-Cache."]
    #[inline(always)]
    pub fn l2_ibus0_cnt_ena(&self) -> L2_IBUS0_CNT_ENA_R {
        L2_IBUS0_CNT_ENA_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - The bit is used to enable ibus1 counter in L2-Cache."]
    #[inline(always)]
    pub fn l2_ibus1_cnt_ena(&self) -> L2_IBUS1_CNT_ENA_R {
        L2_IBUS1_CNT_ENA_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Reserved"]
    #[inline(always)]
    pub fn l2_ibus2_cnt_ena(&self) -> L2_IBUS2_CNT_ENA_R {
        L2_IBUS2_CNT_ENA_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Reserved"]
    #[inline(always)]
    pub fn l2_ibus3_cnt_ena(&self) -> L2_IBUS3_CNT_ENA_R {
        L2_IBUS3_CNT_ENA_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - The bit is used to enable dbus0 counter in L2-Cache."]
    #[inline(always)]
    pub fn l2_dbus0_cnt_ena(&self) -> L2_DBUS0_CNT_ENA_R {
        L2_DBUS0_CNT_ENA_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - The bit is used to enable dbus1 counter in L2-Cache."]
    #[inline(always)]
    pub fn l2_dbus1_cnt_ena(&self) -> L2_DBUS1_CNT_ENA_R {
        L2_DBUS1_CNT_ENA_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Reserved"]
    #[inline(always)]
    pub fn l2_dbus2_cnt_ena(&self) -> L2_DBUS2_CNT_ENA_R {
        L2_DBUS2_CNT_ENA_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Reserved"]
    #[inline(always)]
    pub fn l2_dbus3_cnt_ena(&self) -> L2_DBUS3_CNT_ENA_R {
        L2_DBUS3_CNT_ENA_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 24 - The bit is used to clear ibus0 counter in L2-Cache."]
    #[inline(always)]
    pub fn l2_ibus0_cnt_clr(&self) -> L2_IBUS0_CNT_CLR_R {
        L2_IBUS0_CNT_CLR_R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - The bit is used to clear ibus1 counter in L2-Cache."]
    #[inline(always)]
    pub fn l2_ibus1_cnt_clr(&self) -> L2_IBUS1_CNT_CLR_R {
        L2_IBUS1_CNT_CLR_R::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - Reserved"]
    #[inline(always)]
    pub fn l2_ibus2_cnt_clr(&self) -> L2_IBUS2_CNT_CLR_R {
        L2_IBUS2_CNT_CLR_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - Reserved"]
    #[inline(always)]
    pub fn l2_ibus3_cnt_clr(&self) -> L2_IBUS3_CNT_CLR_R {
        L2_IBUS3_CNT_CLR_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - The bit is used to clear dbus0 counter in L2-Cache."]
    #[inline(always)]
    pub fn l2_dbus0_cnt_clr(&self) -> L2_DBUS0_CNT_CLR_R {
        L2_DBUS0_CNT_CLR_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - The bit is used to clear dbus1 counter in L2-Cache."]
    #[inline(always)]
    pub fn l2_dbus1_cnt_clr(&self) -> L2_DBUS1_CNT_CLR_R {
        L2_DBUS1_CNT_CLR_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - Reserved"]
    #[inline(always)]
    pub fn l2_dbus2_cnt_clr(&self) -> L2_DBUS2_CNT_CLR_R {
        L2_DBUS2_CNT_CLR_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - Reserved"]
    #[inline(always)]
    pub fn l2_dbus3_cnt_clr(&self) -> L2_DBUS3_CNT_CLR_R {
        L2_DBUS3_CNT_CLR_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("L2_CACHE_ACS_CNT_CTRL")
            .field("l2_ibus0_cnt_ena", &self.l2_ibus0_cnt_ena())
            .field("l2_ibus1_cnt_ena", &self.l2_ibus1_cnt_ena())
            .field("l2_ibus2_cnt_ena", &self.l2_ibus2_cnt_ena())
            .field("l2_ibus3_cnt_ena", &self.l2_ibus3_cnt_ena())
            .field("l2_dbus0_cnt_ena", &self.l2_dbus0_cnt_ena())
            .field("l2_dbus1_cnt_ena", &self.l2_dbus1_cnt_ena())
            .field("l2_dbus2_cnt_ena", &self.l2_dbus2_cnt_ena())
            .field("l2_dbus3_cnt_ena", &self.l2_dbus3_cnt_ena())
            .field("l2_ibus0_cnt_clr", &self.l2_ibus0_cnt_clr())
            .field("l2_ibus1_cnt_clr", &self.l2_ibus1_cnt_clr())
            .field("l2_ibus2_cnt_clr", &self.l2_ibus2_cnt_clr())
            .field("l2_ibus3_cnt_clr", &self.l2_ibus3_cnt_clr())
            .field("l2_dbus0_cnt_clr", &self.l2_dbus0_cnt_clr())
            .field("l2_dbus1_cnt_clr", &self.l2_dbus1_cnt_clr())
            .field("l2_dbus2_cnt_clr", &self.l2_dbus2_cnt_clr())
            .field("l2_dbus3_cnt_clr", &self.l2_dbus3_cnt_clr())
            .finish()
    }
}
#[doc = "Cache Access Counter enable and clear register\n\nYou can [`read`](crate::Reg::read) this register and get [`l2_cache_acs_cnt_ctrl::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct L2_CACHE_ACS_CNT_CTRL_SPEC;
impl crate::RegisterSpec for L2_CACHE_ACS_CNT_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`l2_cache_acs_cnt_ctrl::R`](R) reader structure"]
impl crate::Readable for L2_CACHE_ACS_CNT_CTRL_SPEC {}
#[doc = "`reset()` method sets L2_CACHE_ACS_CNT_CTRL to value 0"]
impl crate::Resettable for L2_CACHE_ACS_CNT_CTRL_SPEC {}
