#[doc = "Register `POWER_WAIT_TIMER0` reader"]
pub type R = crate::R<POWER_WAIT_TIMER0_SPEC>;
#[doc = "Register `POWER_WAIT_TIMER0` writer"]
pub type W = crate::W<POWER_WAIT_TIMER0_SPEC>;
#[doc = "Field `DG_HP_POWERDOWN_TIMER` reader - need_des"]
pub type DG_HP_POWERDOWN_TIMER_R = crate::FieldReader<u16>;
#[doc = "Field `DG_HP_POWERDOWN_TIMER` writer - need_des"]
pub type DG_HP_POWERDOWN_TIMER_W<'a, REG> = crate::FieldWriter<'a, REG, 9, u16>;
#[doc = "Field `DG_HP_POWERUP_TIMER` reader - need_des"]
pub type DG_HP_POWERUP_TIMER_R = crate::FieldReader<u16>;
#[doc = "Field `DG_HP_POWERUP_TIMER` writer - need_des"]
pub type DG_HP_POWERUP_TIMER_W<'a, REG> = crate::FieldWriter<'a, REG, 9, u16>;
#[doc = "Field `DG_HP_WAIT_TIMER` reader - need_des"]
pub type DG_HP_WAIT_TIMER_R = crate::FieldReader<u16>;
#[doc = "Field `DG_HP_WAIT_TIMER` writer - need_des"]
pub type DG_HP_WAIT_TIMER_W<'a, REG> = crate::FieldWriter<'a, REG, 9, u16>;
impl R {
    #[doc = "Bits 5:13 - need_des"]
    #[inline(always)]
    pub fn dg_hp_powerdown_timer(&self) -> DG_HP_POWERDOWN_TIMER_R {
        DG_HP_POWERDOWN_TIMER_R::new(((self.bits >> 5) & 0x01ff) as u16)
    }
    #[doc = "Bits 14:22 - need_des"]
    #[inline(always)]
    pub fn dg_hp_powerup_timer(&self) -> DG_HP_POWERUP_TIMER_R {
        DG_HP_POWERUP_TIMER_R::new(((self.bits >> 14) & 0x01ff) as u16)
    }
    #[doc = "Bits 23:31 - need_des"]
    #[inline(always)]
    pub fn dg_hp_wait_timer(&self) -> DG_HP_WAIT_TIMER_R {
        DG_HP_WAIT_TIMER_R::new(((self.bits >> 23) & 0x01ff) as u16)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("POWER_WAIT_TIMER0")
            .field("dg_hp_powerdown_timer", &self.dg_hp_powerdown_timer())
            .field("dg_hp_powerup_timer", &self.dg_hp_powerup_timer())
            .field("dg_hp_wait_timer", &self.dg_hp_wait_timer())
            .finish()
    }
}
impl W {
    #[doc = "Bits 5:13 - need_des"]
    #[inline(always)]
    pub fn dg_hp_powerdown_timer(&mut self) -> DG_HP_POWERDOWN_TIMER_W<'_, POWER_WAIT_TIMER0_SPEC> {
        DG_HP_POWERDOWN_TIMER_W::new(self, 5)
    }
    #[doc = "Bits 14:22 - need_des"]
    #[inline(always)]
    pub fn dg_hp_powerup_timer(&mut self) -> DG_HP_POWERUP_TIMER_W<'_, POWER_WAIT_TIMER0_SPEC> {
        DG_HP_POWERUP_TIMER_W::new(self, 14)
    }
    #[doc = "Bits 23:31 - need_des"]
    #[inline(always)]
    pub fn dg_hp_wait_timer(&mut self) -> DG_HP_WAIT_TIMER_W<'_, POWER_WAIT_TIMER0_SPEC> {
        DG_HP_WAIT_TIMER_W::new(self, 23)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`power_wait_timer0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`power_wait_timer0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct POWER_WAIT_TIMER0_SPEC;
impl crate::RegisterSpec for POWER_WAIT_TIMER0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`power_wait_timer0::R`](R) reader structure"]
impl crate::Readable for POWER_WAIT_TIMER0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`power_wait_timer0::W`](W) writer structure"]
impl crate::Writable for POWER_WAIT_TIMER0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets POWER_WAIT_TIMER0 to value 0x7fbf_dfe0"]
impl crate::Resettable for POWER_WAIT_TIMER0_SPEC {
    const RESET_VALUE: u32 = 0x7fbf_dfe0;
}
