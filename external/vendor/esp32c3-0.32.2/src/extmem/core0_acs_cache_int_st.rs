#[doc = "Register `CORE0_ACS_CACHE_INT_ST` reader"]
pub type R = crate::R<CORE0_ACS_CACHE_INT_ST_SPEC>;
#[doc = "Field `CORE0_IBUS_ACS_MSK_ICACHE` reader - The bit is used to indicate interrupt by cpu access icache while the core0_ibus is disabled or icache is disabled which include speculative access."]
pub type CORE0_IBUS_ACS_MSK_ICACHE_R = crate::BitReader;
#[doc = "Field `CORE0_IBUS_WR_ICACHE` reader - The bit is used to indicate interrupt by ibus trying to write icache"]
pub type CORE0_IBUS_WR_ICACHE_R = crate::BitReader;
#[doc = "Field `CORE0_IBUS_REJECT` reader - The bit is used to indicate interrupt by authentication fail."]
pub type CORE0_IBUS_REJECT_R = crate::BitReader;
#[doc = "Field `CORE0_DBUS_ACS_MSK_ICACHE` reader - The bit is used to indicate interrupt by cpu access icache while the core0_dbus is disabled or icache is disabled which include speculative access."]
pub type CORE0_DBUS_ACS_MSK_ICACHE_R = crate::BitReader;
#[doc = "Field `CORE0_DBUS_REJECT` reader - The bit is used to indicate interrupt by authentication fail."]
pub type CORE0_DBUS_REJECT_R = crate::BitReader;
#[doc = "Field `CORE0_DBUS_WR_ICACHE` reader - The bit is used to indicate interrupt by dbus trying to write icache"]
pub type CORE0_DBUS_WR_ICACHE_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - The bit is used to indicate interrupt by cpu access icache while the core0_ibus is disabled or icache is disabled which include speculative access."]
    #[inline(always)]
    pub fn core0_ibus_acs_msk_icache(&self) -> CORE0_IBUS_ACS_MSK_ICACHE_R {
        CORE0_IBUS_ACS_MSK_ICACHE_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The bit is used to indicate interrupt by ibus trying to write icache"]
    #[inline(always)]
    pub fn core0_ibus_wr_icache(&self) -> CORE0_IBUS_WR_ICACHE_R {
        CORE0_IBUS_WR_ICACHE_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - The bit is used to indicate interrupt by authentication fail."]
    #[inline(always)]
    pub fn core0_ibus_reject(&self) -> CORE0_IBUS_REJECT_R {
        CORE0_IBUS_REJECT_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - The bit is used to indicate interrupt by cpu access icache while the core0_dbus is disabled or icache is disabled which include speculative access."]
    #[inline(always)]
    pub fn core0_dbus_acs_msk_icache(&self) -> CORE0_DBUS_ACS_MSK_ICACHE_R {
        CORE0_DBUS_ACS_MSK_ICACHE_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - The bit is used to indicate interrupt by authentication fail."]
    #[inline(always)]
    pub fn core0_dbus_reject(&self) -> CORE0_DBUS_REJECT_R {
        CORE0_DBUS_REJECT_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - The bit is used to indicate interrupt by dbus trying to write icache"]
    #[inline(always)]
    pub fn core0_dbus_wr_icache(&self) -> CORE0_DBUS_WR_ICACHE_R {
        CORE0_DBUS_WR_ICACHE_R::new(((self.bits >> 5) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CORE0_ACS_CACHE_INT_ST")
            .field(
                "core0_ibus_acs_msk_icache",
                &self.core0_ibus_acs_msk_icache(),
            )
            .field("core0_ibus_wr_icache", &self.core0_ibus_wr_icache())
            .field("core0_ibus_reject", &self.core0_ibus_reject())
            .field(
                "core0_dbus_acs_msk_icache",
                &self.core0_dbus_acs_msk_icache(),
            )
            .field("core0_dbus_reject", &self.core0_dbus_reject())
            .field("core0_dbus_wr_icache", &self.core0_dbus_wr_icache())
            .finish()
    }
}
#[doc = "This description will be updated in the near future.\n\nYou can [`read`](crate::Reg::read) this register and get [`core0_acs_cache_int_st::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CORE0_ACS_CACHE_INT_ST_SPEC;
impl crate::RegisterSpec for CORE0_ACS_CACHE_INT_ST_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`core0_acs_cache_int_st::R`](R) reader structure"]
impl crate::Readable for CORE0_ACS_CACHE_INT_ST_SPEC {}
#[doc = "`reset()` method sets CORE0_ACS_CACHE_INT_ST to value 0"]
impl crate::Resettable for CORE0_ACS_CACHE_INT_ST_SPEC {}
