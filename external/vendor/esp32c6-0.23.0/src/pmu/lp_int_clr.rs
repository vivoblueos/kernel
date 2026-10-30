#[doc = "Register `LP_INT_CLR` writer"]
pub type W = crate::W<LP_INT_CLR_SPEC>;
#[doc = "Field `LP_CPU_WAKEUP` writer - need_des"]
pub type LP_CPU_WAKEUP_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `MODEM_SWITCH_ACTIVE_END` writer - need_des"]
pub type MODEM_SWITCH_ACTIVE_END_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `SLEEP_SWITCH_ACTIVE_END` writer - need_des"]
pub type SLEEP_SWITCH_ACTIVE_END_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `SLEEP_SWITCH_MODEM_END` writer - need_des"]
pub type SLEEP_SWITCH_MODEM_END_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `MODEM_SWITCH_SLEEP_END` writer - need_des"]
pub type MODEM_SWITCH_SLEEP_END_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `ACTIVE_SWITCH_SLEEP_END` writer - need_des"]
pub type ACTIVE_SWITCH_SLEEP_END_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `MODEM_SWITCH_ACTIVE_START` writer - need_des"]
pub type MODEM_SWITCH_ACTIVE_START_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `SLEEP_SWITCH_ACTIVE_START` writer - need_des"]
pub type SLEEP_SWITCH_ACTIVE_START_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `SLEEP_SWITCH_MODEM_START` writer - need_des"]
pub type SLEEP_SWITCH_MODEM_START_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `MODEM_SWITCH_SLEEP_START` writer - need_des"]
pub type MODEM_SWITCH_SLEEP_START_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `ACTIVE_SWITCH_SLEEP_START` writer - need_des"]
pub type ACTIVE_SWITCH_SLEEP_START_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `HP_SW_TRIGGER` writer - need_des"]
pub type HP_SW_TRIGGER_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<LP_INT_CLR_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 20 - need_des"]
    #[inline(always)]
    pub fn lp_cpu_wakeup(&mut self) -> LP_CPU_WAKEUP_W<'_, LP_INT_CLR_SPEC> {
        LP_CPU_WAKEUP_W::new(self, 20)
    }
    #[doc = "Bit 21 - need_des"]
    #[inline(always)]
    pub fn modem_switch_active_end(&mut self) -> MODEM_SWITCH_ACTIVE_END_W<'_, LP_INT_CLR_SPEC> {
        MODEM_SWITCH_ACTIVE_END_W::new(self, 21)
    }
    #[doc = "Bit 22 - need_des"]
    #[inline(always)]
    pub fn sleep_switch_active_end(&mut self) -> SLEEP_SWITCH_ACTIVE_END_W<'_, LP_INT_CLR_SPEC> {
        SLEEP_SWITCH_ACTIVE_END_W::new(self, 22)
    }
    #[doc = "Bit 23 - need_des"]
    #[inline(always)]
    pub fn sleep_switch_modem_end(&mut self) -> SLEEP_SWITCH_MODEM_END_W<'_, LP_INT_CLR_SPEC> {
        SLEEP_SWITCH_MODEM_END_W::new(self, 23)
    }
    #[doc = "Bit 24 - need_des"]
    #[inline(always)]
    pub fn modem_switch_sleep_end(&mut self) -> MODEM_SWITCH_SLEEP_END_W<'_, LP_INT_CLR_SPEC> {
        MODEM_SWITCH_SLEEP_END_W::new(self, 24)
    }
    #[doc = "Bit 25 - need_des"]
    #[inline(always)]
    pub fn active_switch_sleep_end(&mut self) -> ACTIVE_SWITCH_SLEEP_END_W<'_, LP_INT_CLR_SPEC> {
        ACTIVE_SWITCH_SLEEP_END_W::new(self, 25)
    }
    #[doc = "Bit 26 - need_des"]
    #[inline(always)]
    pub fn modem_switch_active_start(
        &mut self,
    ) -> MODEM_SWITCH_ACTIVE_START_W<'_, LP_INT_CLR_SPEC> {
        MODEM_SWITCH_ACTIVE_START_W::new(self, 26)
    }
    #[doc = "Bit 27 - need_des"]
    #[inline(always)]
    pub fn sleep_switch_active_start(
        &mut self,
    ) -> SLEEP_SWITCH_ACTIVE_START_W<'_, LP_INT_CLR_SPEC> {
        SLEEP_SWITCH_ACTIVE_START_W::new(self, 27)
    }
    #[doc = "Bit 28 - need_des"]
    #[inline(always)]
    pub fn sleep_switch_modem_start(&mut self) -> SLEEP_SWITCH_MODEM_START_W<'_, LP_INT_CLR_SPEC> {
        SLEEP_SWITCH_MODEM_START_W::new(self, 28)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn modem_switch_sleep_start(&mut self) -> MODEM_SWITCH_SLEEP_START_W<'_, LP_INT_CLR_SPEC> {
        MODEM_SWITCH_SLEEP_START_W::new(self, 29)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn active_switch_sleep_start(
        &mut self,
    ) -> ACTIVE_SWITCH_SLEEP_START_W<'_, LP_INT_CLR_SPEC> {
        ACTIVE_SWITCH_SLEEP_START_W::new(self, 30)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn hp_sw_trigger(&mut self) -> HP_SW_TRIGGER_W<'_, LP_INT_CLR_SPEC> {
        HP_SW_TRIGGER_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`lp_int_clr::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LP_INT_CLR_SPEC;
impl crate::RegisterSpec for LP_INT_CLR_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`lp_int_clr::W`](W) writer structure"]
impl crate::Writable for LP_INT_CLR_SPEC {
    type Safety = crate::Unsafe;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0xfff0_0000;
}
#[doc = "`reset()` method sets LP_INT_CLR to value 0"]
impl crate::Resettable for LP_INT_CLR_SPEC {}
