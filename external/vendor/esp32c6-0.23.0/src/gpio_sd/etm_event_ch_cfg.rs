#[doc = "Register `ETM_EVENT_CH%s_CFG` reader"]
pub type R = crate::R<ETM_EVENT_CH_CFG_SPEC>;
#[doc = "Register `ETM_EVENT_CH%s_CFG` writer"]
pub type W = crate::W<ETM_EVENT_CH_CFG_SPEC>;
#[doc = "Field `EVENT_SEL` reader - Etm event channel select gpio."]
pub type EVENT_SEL_R = crate::FieldReader;
#[doc = "Field `EVENT_SEL` writer - Etm event channel select gpio."]
pub type EVENT_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `EVENT_EN` reader - Etm event send enable bit."]
pub type EVENT_EN_R = crate::BitReader;
#[doc = "Field `EVENT_EN` writer - Etm event send enable bit."]
pub type EVENT_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:4 - Etm event channel select gpio."]
    #[inline(always)]
    pub fn event_sel(&self) -> EVENT_SEL_R {
        EVENT_SEL_R::new((self.bits & 0x1f) as u8)
    }
    #[doc = "Bit 7 - Etm event send enable bit."]
    #[inline(always)]
    pub fn event_en(&self) -> EVENT_EN_R {
        EVENT_EN_R::new(((self.bits >> 7) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("ETM_EVENT_CH_CFG")
            .field("event_sel", &self.event_sel())
            .field("event_en", &self.event_en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:4 - Etm event channel select gpio."]
    #[inline(always)]
    pub fn event_sel(&mut self) -> EVENT_SEL_W<'_, ETM_EVENT_CH_CFG_SPEC> {
        EVENT_SEL_W::new(self, 0)
    }
    #[doc = "Bit 7 - Etm event send enable bit."]
    #[inline(always)]
    pub fn event_en(&mut self) -> EVENT_EN_W<'_, ETM_EVENT_CH_CFG_SPEC> {
        EVENT_EN_W::new(self, 7)
    }
}
#[doc = "Etm Config register of Channel%s\n\nYou can [`read`](crate::Reg::read) this register and get [`etm_event_ch_cfg::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`etm_event_ch_cfg::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ETM_EVENT_CH_CFG_SPEC;
impl crate::RegisterSpec for ETM_EVENT_CH_CFG_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`etm_event_ch_cfg::R`](R) reader structure"]
impl crate::Readable for ETM_EVENT_CH_CFG_SPEC {}
#[doc = "`write(|w| ..)` method takes [`etm_event_ch_cfg::W`](W) writer structure"]
impl crate::Writable for ETM_EVENT_CH_CFG_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets ETM_EVENT_CH%s_CFG to value 0"]
impl crate::Resettable for ETM_EVENT_CH_CFG_SPEC {}
