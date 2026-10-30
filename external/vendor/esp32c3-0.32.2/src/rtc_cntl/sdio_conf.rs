#[doc = "Register `SDIO_CONF` reader"]
pub type R = crate::R<SDIO_CONF_SPEC>;
#[doc = "Register `SDIO_CONF` writer"]
pub type W = crate::W<SDIO_CONF_SPEC>;
#[doc = "Field `SDIO_TIMER_TARGET` reader - timer count to apply reg_sdio_dcap after sdio power on"]
pub type SDIO_TIMER_TARGET_R = crate::FieldReader;
#[doc = "Field `SDIO_TIMER_TARGET` writer - timer count to apply reg_sdio_dcap after sdio power on"]
pub type SDIO_TIMER_TARGET_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `SDIO_DTHDRV` reader - Tieh = 1 mode drive ability. Initially set to 0 to limit charge current"]
pub type SDIO_DTHDRV_R = crate::FieldReader;
#[doc = "Field `SDIO_DTHDRV` writer - Tieh = 1 mode drive ability. Initially set to 0 to limit charge current"]
pub type SDIO_DTHDRV_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `SDIO_DCAP` reader - ability to prevent LDO from overshoot"]
pub type SDIO_DCAP_R = crate::FieldReader;
#[doc = "Field `SDIO_DCAP` writer - ability to prevent LDO from overshoot"]
pub type SDIO_DCAP_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `SDIO_INITI` reader - add resistor from ldo output to ground. 0: no res"]
pub type SDIO_INITI_R = crate::FieldReader;
#[doc = "Field `SDIO_INITI` writer - add resistor from ldo output to ground. 0: no res"]
pub type SDIO_INITI_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `SDIO_EN_INITI` reader - 0 to set init\\[1:0\\]=0"]
pub type SDIO_EN_INITI_R = crate::BitReader;
#[doc = "Field `SDIO_EN_INITI` writer - 0 to set init\\[1:0\\]=0"]
pub type SDIO_EN_INITI_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_DCURLIM` reader - tune current limit threshold when tieh = 0. About 800mA/(8+d)"]
pub type SDIO_DCURLIM_R = crate::FieldReader;
#[doc = "Field `SDIO_DCURLIM` writer - tune current limit threshold when tieh = 0. About 800mA/(8+d)"]
pub type SDIO_DCURLIM_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `SDIO_MODECURLIM` reader - select current limit mode"]
pub type SDIO_MODECURLIM_R = crate::BitReader;
#[doc = "Field `SDIO_MODECURLIM` writer - select current limit mode"]
pub type SDIO_MODECURLIM_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_ENCURLIM` reader - enable current limit"]
pub type SDIO_ENCURLIM_R = crate::BitReader;
#[doc = "Field `SDIO_ENCURLIM` writer - enable current limit"]
pub type SDIO_ENCURLIM_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_REG_PD_EN` reader - power down SDIO_REG in sleep. Only active when reg_sdio_force = 0"]
pub type SDIO_REG_PD_EN_R = crate::BitReader;
#[doc = "Field `SDIO_REG_PD_EN` writer - power down SDIO_REG in sleep. Only active when reg_sdio_force = 0"]
pub type SDIO_REG_PD_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_FORCE` reader - 1: use SW option to control SDIO_REG"]
pub type SDIO_FORCE_R = crate::BitReader;
#[doc = "Field `SDIO_FORCE` writer - 1: use SW option to control SDIO_REG"]
pub type SDIO_FORCE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIO_TIEH` reader - SW option for SDIO_TIEH. Only active when reg_sdio_force = 1"]
pub type SDIO_TIEH_R = crate::BitReader;
#[doc = "Field `SDIO_TIEH` writer - SW option for SDIO_TIEH. Only active when reg_sdio_force = 1"]
pub type SDIO_TIEH_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `_1P8_READY` reader - read only register for REG1P8_READY"]
pub type _1P8_READY_R = crate::BitReader;
#[doc = "Field `DREFL_SDIO` reader - SW option for DREFL_SDIO. Only active when reg_sdio_force = 1"]
pub type DREFL_SDIO_R = crate::FieldReader;
#[doc = "Field `DREFL_SDIO` writer - SW option for DREFL_SDIO. Only active when reg_sdio_force = 1"]
pub type DREFL_SDIO_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `DREFM_SDIO` reader - SW option for DREFM_SDIO. Only active when reg_sdio_force = 1"]
pub type DREFM_SDIO_R = crate::FieldReader;
#[doc = "Field `DREFM_SDIO` writer - SW option for DREFM_SDIO. Only active when reg_sdio_force = 1"]
pub type DREFM_SDIO_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `DREFH_SDIO` reader - SW option for DREFH_SDIO. Only active when reg_sdio_force = 1"]
pub type DREFH_SDIO_R = crate::FieldReader;
#[doc = "Field `DREFH_SDIO` writer - SW option for DREFH_SDIO. Only active when reg_sdio_force = 1"]
pub type DREFH_SDIO_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `XPD_SDIO` reader - "]
pub type XPD_SDIO_R = crate::BitReader;
#[doc = "Field `XPD_SDIO` writer - "]
pub type XPD_SDIO_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:7 - timer count to apply reg_sdio_dcap after sdio power on"]
    #[inline(always)]
    pub fn sdio_timer_target(&self) -> SDIO_TIMER_TARGET_R {
        SDIO_TIMER_TARGET_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 9:10 - Tieh = 1 mode drive ability. Initially set to 0 to limit charge current"]
    #[inline(always)]
    pub fn sdio_dthdrv(&self) -> SDIO_DTHDRV_R {
        SDIO_DTHDRV_R::new(((self.bits >> 9) & 3) as u8)
    }
    #[doc = "Bits 11:12 - ability to prevent LDO from overshoot"]
    #[inline(always)]
    pub fn sdio_dcap(&self) -> SDIO_DCAP_R {
        SDIO_DCAP_R::new(((self.bits >> 11) & 3) as u8)
    }
    #[doc = "Bits 13:14 - add resistor from ldo output to ground. 0: no res"]
    #[inline(always)]
    pub fn sdio_initi(&self) -> SDIO_INITI_R {
        SDIO_INITI_R::new(((self.bits >> 13) & 3) as u8)
    }
    #[doc = "Bit 15 - 0 to set init\\[1:0\\]=0"]
    #[inline(always)]
    pub fn sdio_en_initi(&self) -> SDIO_EN_INITI_R {
        SDIO_EN_INITI_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bits 16:18 - tune current limit threshold when tieh = 0. About 800mA/(8+d)"]
    #[inline(always)]
    pub fn sdio_dcurlim(&self) -> SDIO_DCURLIM_R {
        SDIO_DCURLIM_R::new(((self.bits >> 16) & 7) as u8)
    }
    #[doc = "Bit 19 - select current limit mode"]
    #[inline(always)]
    pub fn sdio_modecurlim(&self) -> SDIO_MODECURLIM_R {
        SDIO_MODECURLIM_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - enable current limit"]
    #[inline(always)]
    pub fn sdio_encurlim(&self) -> SDIO_ENCURLIM_R {
        SDIO_ENCURLIM_R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - power down SDIO_REG in sleep. Only active when reg_sdio_force = 0"]
    #[inline(always)]
    pub fn sdio_reg_pd_en(&self) -> SDIO_REG_PD_EN_R {
        SDIO_REG_PD_EN_R::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 22 - 1: use SW option to control SDIO_REG"]
    #[inline(always)]
    pub fn sdio_force(&self) -> SDIO_FORCE_R {
        SDIO_FORCE_R::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 23 - SW option for SDIO_TIEH. Only active when reg_sdio_force = 1"]
    #[inline(always)]
    pub fn sdio_tieh(&self) -> SDIO_TIEH_R {
        SDIO_TIEH_R::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bit 24 - read only register for REG1P8_READY"]
    #[inline(always)]
    pub fn _1p8_ready(&self) -> _1P8_READY_R {
        _1P8_READY_R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bits 25:26 - SW option for DREFL_SDIO. Only active when reg_sdio_force = 1"]
    #[inline(always)]
    pub fn drefl_sdio(&self) -> DREFL_SDIO_R {
        DREFL_SDIO_R::new(((self.bits >> 25) & 3) as u8)
    }
    #[doc = "Bits 27:28 - SW option for DREFM_SDIO. Only active when reg_sdio_force = 1"]
    #[inline(always)]
    pub fn drefm_sdio(&self) -> DREFM_SDIO_R {
        DREFM_SDIO_R::new(((self.bits >> 27) & 3) as u8)
    }
    #[doc = "Bits 29:30 - SW option for DREFH_SDIO. Only active when reg_sdio_force = 1"]
    #[inline(always)]
    pub fn drefh_sdio(&self) -> DREFH_SDIO_R {
        DREFH_SDIO_R::new(((self.bits >> 29) & 3) as u8)
    }
    #[doc = "Bit 31"]
    #[inline(always)]
    pub fn xpd_sdio(&self) -> XPD_SDIO_R {
        XPD_SDIO_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SDIO_CONF")
            .field("sdio_timer_target", &self.sdio_timer_target())
            .field("sdio_dthdrv", &self.sdio_dthdrv())
            .field("sdio_dcap", &self.sdio_dcap())
            .field("sdio_initi", &self.sdio_initi())
            .field("sdio_en_initi", &self.sdio_en_initi())
            .field("sdio_dcurlim", &self.sdio_dcurlim())
            .field("sdio_modecurlim", &self.sdio_modecurlim())
            .field("sdio_encurlim", &self.sdio_encurlim())
            .field("sdio_reg_pd_en", &self.sdio_reg_pd_en())
            .field("sdio_force", &self.sdio_force())
            .field("sdio_tieh", &self.sdio_tieh())
            .field("_1p8_ready", &self._1p8_ready())
            .field("drefl_sdio", &self.drefl_sdio())
            .field("drefm_sdio", &self.drefm_sdio())
            .field("drefh_sdio", &self.drefh_sdio())
            .field("xpd_sdio", &self.xpd_sdio())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - timer count to apply reg_sdio_dcap after sdio power on"]
    #[inline(always)]
    pub fn sdio_timer_target(&mut self) -> SDIO_TIMER_TARGET_W<'_, SDIO_CONF_SPEC> {
        SDIO_TIMER_TARGET_W::new(self, 0)
    }
    #[doc = "Bits 9:10 - Tieh = 1 mode drive ability. Initially set to 0 to limit charge current"]
    #[inline(always)]
    pub fn sdio_dthdrv(&mut self) -> SDIO_DTHDRV_W<'_, SDIO_CONF_SPEC> {
        SDIO_DTHDRV_W::new(self, 9)
    }
    #[doc = "Bits 11:12 - ability to prevent LDO from overshoot"]
    #[inline(always)]
    pub fn sdio_dcap(&mut self) -> SDIO_DCAP_W<'_, SDIO_CONF_SPEC> {
        SDIO_DCAP_W::new(self, 11)
    }
    #[doc = "Bits 13:14 - add resistor from ldo output to ground. 0: no res"]
    #[inline(always)]
    pub fn sdio_initi(&mut self) -> SDIO_INITI_W<'_, SDIO_CONF_SPEC> {
        SDIO_INITI_W::new(self, 13)
    }
    #[doc = "Bit 15 - 0 to set init\\[1:0\\]=0"]
    #[inline(always)]
    pub fn sdio_en_initi(&mut self) -> SDIO_EN_INITI_W<'_, SDIO_CONF_SPEC> {
        SDIO_EN_INITI_W::new(self, 15)
    }
    #[doc = "Bits 16:18 - tune current limit threshold when tieh = 0. About 800mA/(8+d)"]
    #[inline(always)]
    pub fn sdio_dcurlim(&mut self) -> SDIO_DCURLIM_W<'_, SDIO_CONF_SPEC> {
        SDIO_DCURLIM_W::new(self, 16)
    }
    #[doc = "Bit 19 - select current limit mode"]
    #[inline(always)]
    pub fn sdio_modecurlim(&mut self) -> SDIO_MODECURLIM_W<'_, SDIO_CONF_SPEC> {
        SDIO_MODECURLIM_W::new(self, 19)
    }
    #[doc = "Bit 20 - enable current limit"]
    #[inline(always)]
    pub fn sdio_encurlim(&mut self) -> SDIO_ENCURLIM_W<'_, SDIO_CONF_SPEC> {
        SDIO_ENCURLIM_W::new(self, 20)
    }
    #[doc = "Bit 21 - power down SDIO_REG in sleep. Only active when reg_sdio_force = 0"]
    #[inline(always)]
    pub fn sdio_reg_pd_en(&mut self) -> SDIO_REG_PD_EN_W<'_, SDIO_CONF_SPEC> {
        SDIO_REG_PD_EN_W::new(self, 21)
    }
    #[doc = "Bit 22 - 1: use SW option to control SDIO_REG"]
    #[inline(always)]
    pub fn sdio_force(&mut self) -> SDIO_FORCE_W<'_, SDIO_CONF_SPEC> {
        SDIO_FORCE_W::new(self, 22)
    }
    #[doc = "Bit 23 - SW option for SDIO_TIEH. Only active when reg_sdio_force = 1"]
    #[inline(always)]
    pub fn sdio_tieh(&mut self) -> SDIO_TIEH_W<'_, SDIO_CONF_SPEC> {
        SDIO_TIEH_W::new(self, 23)
    }
    #[doc = "Bits 25:26 - SW option for DREFL_SDIO. Only active when reg_sdio_force = 1"]
    #[inline(always)]
    pub fn drefl_sdio(&mut self) -> DREFL_SDIO_W<'_, SDIO_CONF_SPEC> {
        DREFL_SDIO_W::new(self, 25)
    }
    #[doc = "Bits 27:28 - SW option for DREFM_SDIO. Only active when reg_sdio_force = 1"]
    #[inline(always)]
    pub fn drefm_sdio(&mut self) -> DREFM_SDIO_W<'_, SDIO_CONF_SPEC> {
        DREFM_SDIO_W::new(self, 27)
    }
    #[doc = "Bits 29:30 - SW option for DREFH_SDIO. Only active when reg_sdio_force = 1"]
    #[inline(always)]
    pub fn drefh_sdio(&mut self) -> DREFH_SDIO_W<'_, SDIO_CONF_SPEC> {
        DREFH_SDIO_W::new(self, 29)
    }
    #[doc = "Bit 31"]
    #[inline(always)]
    pub fn xpd_sdio(&mut self) -> XPD_SDIO_W<'_, SDIO_CONF_SPEC> {
        XPD_SDIO_W::new(self, 31)
    }
}
#[doc = "rtc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`sdio_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`sdio_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SDIO_CONF_SPEC;
impl crate::RegisterSpec for SDIO_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sdio_conf::R`](R) reader structure"]
impl crate::Readable for SDIO_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`sdio_conf::W`](W) writer structure"]
impl crate::Writable for SDIO_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SDIO_CONF to value 0x0ab0_be0a"]
impl crate::Resettable for SDIO_CONF_SPEC {
    const RESET_VALUE: u32 = 0x0ab0_be0a;
}
