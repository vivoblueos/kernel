#[doc = "Register `TARGET%s_CONF` reader"]
pub type R = crate::R<TARGET_CONF_SPEC>;
#[doc = "Register `TARGET%s_CONF` writer"]
pub type W = crate::W<TARGET_CONF_SPEC>;
#[doc = "Field `PERIOD` reader - target0 period"]
pub type PERIOD_R = crate::FieldReader<u32>;
#[doc = "Field `PERIOD` writer - target0 period"]
pub type PERIOD_W<'a, REG> = crate::FieldWriter<'a, REG, 26, u32>;
#[doc = "Field `PERIOD_MODE` reader - Set target0 to period mode"]
pub type PERIOD_MODE_R = crate::BitReader;
#[doc = "Field `PERIOD_MODE` writer - Set target0 to period mode"]
pub type PERIOD_MODE_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER_UNIT_SEL` reader - select which unit to compare"]
pub type TIMER_UNIT_SEL_R = crate::BitReader;
#[doc = "Field `TIMER_UNIT_SEL` writer - select which unit to compare"]
pub type TIMER_UNIT_SEL_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:25 - target0 period"]
    #[inline(always)]
    pub fn period(&self) -> PERIOD_R {
        PERIOD_R::new(self.bits & 0x03ff_ffff)
    }
    #[doc = "Bit 30 - Set target0 to period mode"]
    #[inline(always)]
    pub fn period_mode(&self) -> PERIOD_MODE_R {
        PERIOD_MODE_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - select which unit to compare"]
    #[inline(always)]
    pub fn timer_unit_sel(&self) -> TIMER_UNIT_SEL_R {
        TIMER_UNIT_SEL_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("TARGET_CONF")
            .field("period", &self.period())
            .field("period_mode", &self.period_mode())
            .field("timer_unit_sel", &self.timer_unit_sel())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:25 - target0 period"]
    #[inline(always)]
    pub fn period(&mut self) -> PERIOD_W<'_, TARGET_CONF_SPEC> {
        PERIOD_W::new(self, 0)
    }
    #[doc = "Bit 30 - Set target0 to period mode"]
    #[inline(always)]
    pub fn period_mode(&mut self) -> PERIOD_MODE_W<'_, TARGET_CONF_SPEC> {
        PERIOD_MODE_W::new(self, 30)
    }
    #[doc = "Bit 31 - select which unit to compare"]
    #[inline(always)]
    pub fn timer_unit_sel(&mut self) -> TIMER_UNIT_SEL_W<'_, TARGET_CONF_SPEC> {
        TIMER_UNIT_SEL_W::new(self, 31)
    }
}
#[doc = "system timer comp%s target mode register\n\nYou can [`read`](crate::Reg::read) this register and get [`target_conf::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`target_conf::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TARGET_CONF_SPEC;
impl crate::RegisterSpec for TARGET_CONF_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`target_conf::R`](R) reader structure"]
impl crate::Readable for TARGET_CONF_SPEC {}
#[doc = "`write(|w| ..)` method takes [`target_conf::W`](W) writer structure"]
impl crate::Writable for TARGET_CONF_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets TARGET%s_CONF to value 0"]
impl crate::Resettable for TARGET_CONF_SPEC {}
