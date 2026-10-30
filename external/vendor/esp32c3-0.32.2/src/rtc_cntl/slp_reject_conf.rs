#[doc = "Register `SLP_REJECT_CONF` reader"]
pub type R = crate::R<SLP_REJECT_CONF_SPEC>;
#[doc = "Register `SLP_REJECT_CONF` writer"]
pub type W = crate::W<SLP_REJECT_CONF_SPEC>;
#[doc = "Field `SLEEP_REJECT_ENA` reader - sleep reject enable"]
pub type SLEEP_REJECT_ENA_R = crate::FieldReader<u32>;
#[doc = "Field `SLEEP_REJECT_ENA` writer - sleep reject enable"]
pub type SLEEP_REJECT_ENA_W<'a, REG> = crate::FieldWriter<'a, REG, 18, u32>;
#[doc = "Field `LIGHT_SLP_REJECT_EN` reader - enable reject for light sleep"]
pub type LIGHT_SLP_REJECT_EN_R = crate::BitReader;
#[doc = "Field `LIGHT_SLP_REJECT_EN` writer - enable reject for light sleep"]
pub type LIGHT_SLP_REJECT_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DEEP_SLP_REJECT_EN` reader - enable reject for deep sleep"]
pub type DEEP_SLP_REJECT_EN_R = crate::BitReader;
#[doc = "Field `DEEP_SLP_REJECT_EN` writer - enable reject for deep sleep"]
pub type DEEP_SLP_REJECT_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 12:29 - sleep reject enable"]
    #[inline(always)]
    pub fn sleep_reject_ena(&self) -> SLEEP_REJECT_ENA_R {
        SLEEP_REJECT_ENA_R::new((self.bits >> 12) & 0x0003_ffff)
    }
    #[doc = "Bit 30 - enable reject for light sleep"]
    #[inline(always)]
    pub fn light_slp_reject_en(&self) -> LIGHT_SLP_REJECT_EN_R {
        LIGHT_SLP_REJECT_EN_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - enable reject for deep sleep"]
    #[inline(always)]
    pub fn deep_slp_reject_en(&self) -> DEEP_SLP_REJECT_EN_R {
        DEEP_SLP_REJECT_EN_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("SLP_REJECT_CONF")
            .field("sleep_reject_ena", &self.sleep_reject_ena())
            .field("light_slp_reject_en", &self.light_slp_reject_en())
            .field("deep_slp_reject_en", &self.deep_slp_reject_en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 12:29 - sleep reject enable"]
    #[inline(always)]
    pub fn sleep_reject_ena(&mut self) -> SLEEP_REJECT_ENA_W<'_, SLP_REJECT_CONF_SPEC> {
        SLEEP_REJECT_ENA_W::new(self, 12)
    }
    #[doc = "Bit 30 - enable reject for light sleep"]
    #[inline(always)]
    pub fn light_slp_reject_en(&mut self) -> LIGHT_SLP_REJECT_EN_W<'_, SLP_REJECT_CONF_SPEC> {
        LIGHT_SLP_REJECT_EN_W::new(self, 30)
    }
    #[doc = "Bit 31 - enable reject for deep sleep"]
    #[inline(always)]
    pub fn deep_slp_reject_en(&mut self) -> DEEP_SLP_REJECT_EN_W<'_, SLP_REJECT_CONF_SPEC> {
        DEEP_SLP_REJECT_EN_W::new(self, 31)
    }
}
#[doc = "rtc configure register\n\nYou can [`read`](crate::Reg::read) this register and get [`slp_reject_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`slp_reject_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SLP_REJECT_CONF_SPEC;
impl crate::RegisterSpec for SLP_REJECT_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`slp_reject_conf::R`](R) reader structure"]
impl crate::Readable for SLP_REJECT_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`slp_reject_conf::W`](W) writer structure"]
impl crate::Writable for SLP_REJECT_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets SLP_REJECT_CONF to value 0"]
impl crate::Resettable for SLP_REJECT_CONF_SPEC {}
