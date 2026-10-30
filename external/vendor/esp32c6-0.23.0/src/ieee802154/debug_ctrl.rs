#[doc = "Register `DEBUG_CTRL` reader"]
pub type R = crate::R<DEBUG_CTRL_SPEC>;
#[doc = "Register `DEBUG_CTRL` writer"]
pub type W = crate::W<DEBUG_CTRL_SPEC>;
#[doc = "Field `DEBUG_SIGNAL_SEL` reader - "]
pub type DEBUG_SIGNAL_SEL_R = crate::FieldReader;
#[doc = "Field `DEBUG_SIGNAL_SEL` writer - "]
pub type DEBUG_SIGNAL_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `DEBUG_TRIGGER_STATE_SELECT` reader - "]
pub type DEBUG_TRIGGER_STATE_SELECT_R = crate::FieldReader;
#[doc = "Field `DEBUG_TRIGGER_STATE_SELECT` writer - "]
pub type DEBUG_TRIGGER_STATE_SELECT_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `DEBUG_SER_DEBUG_SEL` reader - "]
pub type DEBUG_SER_DEBUG_SEL_R = crate::FieldReader;
#[doc = "Field `DEBUG_SER_DEBUG_SEL` writer - "]
pub type DEBUG_SER_DEBUG_SEL_W<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `DEBUG_TRIGGER_STATE_MATCH_VALUE` reader - "]
pub type DEBUG_TRIGGER_STATE_MATCH_VALUE_R = crate::FieldReader;
#[doc = "Field `DEBUG_TRIGGER_STATE_MATCH_VALUE` writer - "]
pub type DEBUG_TRIGGER_STATE_MATCH_VALUE_W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `DEBUG_TRIGGER_PULSE_SELECT` reader - "]
pub type DEBUG_TRIGGER_PULSE_SELECT_R = crate::FieldReader;
#[doc = "Field `DEBUG_TRIGGER_PULSE_SELECT` writer - "]
pub type DEBUG_TRIGGER_PULSE_SELECT_W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `DEBUG_STATE_MATCH_DUMP_EN` reader - "]
pub type DEBUG_STATE_MATCH_DUMP_EN_R = crate::BitReader;
#[doc = "Field `DEBUG_STATE_MATCH_DUMP_EN` writer - "]
pub type DEBUG_STATE_MATCH_DUMP_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DEBUG_TRIGGER_DUMP_EN` reader - "]
pub type DEBUG_TRIGGER_DUMP_EN_R = crate::BitReader;
#[doc = "Field `DEBUG_TRIGGER_DUMP_EN` writer - "]
pub type DEBUG_TRIGGER_DUMP_EN_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:2"]
    #[inline(always)]
    pub fn debug_signal_sel(&self) -> DEBUG_SIGNAL_SEL_R {
        DEBUG_SIGNAL_SEL_R::new((self.bits & 7) as u8)
    }
    #[doc = "Bits 8:11"]
    #[inline(always)]
    pub fn debug_trigger_state_select(&self) -> DEBUG_TRIGGER_STATE_SELECT_R {
        DEBUG_TRIGGER_STATE_SELECT_R::new(((self.bits >> 8) & 0x0f) as u8)
    }
    #[doc = "Bits 12:15"]
    #[inline(always)]
    pub fn debug_ser_debug_sel(&self) -> DEBUG_SER_DEBUG_SEL_R {
        DEBUG_SER_DEBUG_SEL_R::new(((self.bits >> 12) & 0x0f) as u8)
    }
    #[doc = "Bits 16:20"]
    #[inline(always)]
    pub fn debug_trigger_state_match_value(&self) -> DEBUG_TRIGGER_STATE_MATCH_VALUE_R {
        DEBUG_TRIGGER_STATE_MATCH_VALUE_R::new(((self.bits >> 16) & 0x1f) as u8)
    }
    #[doc = "Bits 24:26"]
    #[inline(always)]
    pub fn debug_trigger_pulse_select(&self) -> DEBUG_TRIGGER_PULSE_SELECT_R {
        DEBUG_TRIGGER_PULSE_SELECT_R::new(((self.bits >> 24) & 7) as u8)
    }
    #[doc = "Bit 30"]
    #[inline(always)]
    pub fn debug_state_match_dump_en(&self) -> DEBUG_STATE_MATCH_DUMP_EN_R {
        DEBUG_STATE_MATCH_DUMP_EN_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31"]
    #[inline(always)]
    pub fn debug_trigger_dump_en(&self) -> DEBUG_TRIGGER_DUMP_EN_R {
        DEBUG_TRIGGER_DUMP_EN_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("DEBUG_CTRL")
            .field("debug_signal_sel", &self.debug_signal_sel())
            .field(
                "debug_trigger_state_select",
                &self.debug_trigger_state_select(),
            )
            .field("debug_ser_debug_sel", &self.debug_ser_debug_sel())
            .field(
                "debug_trigger_state_match_value",
                &self.debug_trigger_state_match_value(),
            )
            .field(
                "debug_trigger_pulse_select",
                &self.debug_trigger_pulse_select(),
            )
            .field(
                "debug_state_match_dump_en",
                &self.debug_state_match_dump_en(),
            )
            .field("debug_trigger_dump_en", &self.debug_trigger_dump_en())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:2"]
    #[inline(always)]
    pub fn debug_signal_sel(&mut self) -> DEBUG_SIGNAL_SEL_W<'_, DEBUG_CTRL_SPEC> {
        DEBUG_SIGNAL_SEL_W::new(self, 0)
    }
    #[doc = "Bits 8:11"]
    #[inline(always)]
    pub fn debug_trigger_state_select(
        &mut self,
    ) -> DEBUG_TRIGGER_STATE_SELECT_W<'_, DEBUG_CTRL_SPEC> {
        DEBUG_TRIGGER_STATE_SELECT_W::new(self, 8)
    }
    #[doc = "Bits 12:15"]
    #[inline(always)]
    pub fn debug_ser_debug_sel(&mut self) -> DEBUG_SER_DEBUG_SEL_W<'_, DEBUG_CTRL_SPEC> {
        DEBUG_SER_DEBUG_SEL_W::new(self, 12)
    }
    #[doc = "Bits 16:20"]
    #[inline(always)]
    pub fn debug_trigger_state_match_value(
        &mut self,
    ) -> DEBUG_TRIGGER_STATE_MATCH_VALUE_W<'_, DEBUG_CTRL_SPEC> {
        DEBUG_TRIGGER_STATE_MATCH_VALUE_W::new(self, 16)
    }
    #[doc = "Bits 24:26"]
    #[inline(always)]
    pub fn debug_trigger_pulse_select(
        &mut self,
    ) -> DEBUG_TRIGGER_PULSE_SELECT_W<'_, DEBUG_CTRL_SPEC> {
        DEBUG_TRIGGER_PULSE_SELECT_W::new(self, 24)
    }
    #[doc = "Bit 30"]
    #[inline(always)]
    pub fn debug_state_match_dump_en(
        &mut self,
    ) -> DEBUG_STATE_MATCH_DUMP_EN_W<'_, DEBUG_CTRL_SPEC> {
        DEBUG_STATE_MATCH_DUMP_EN_W::new(self, 30)
    }
    #[doc = "Bit 31"]
    #[inline(always)]
    pub fn debug_trigger_dump_en(&mut self) -> DEBUG_TRIGGER_DUMP_EN_W<'_, DEBUG_CTRL_SPEC> {
        DEBUG_TRIGGER_DUMP_EN_W::new(self, 31)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`debug_ctrl::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`debug_ctrl::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DEBUG_CTRL_SPEC;
impl crate::RegisterSpec for DEBUG_CTRL_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`debug_ctrl::R`](R) reader structure"]
impl crate::Readable for DEBUG_CTRL_SPEC {}
#[doc = "`write(|w| ..)` method takes [`debug_ctrl::W`](W) writer structure"]
impl crate::Writable for DEBUG_CTRL_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets DEBUG_CTRL to value 0"]
impl crate::Resettable for DEBUG_CTRL_SPEC {}
