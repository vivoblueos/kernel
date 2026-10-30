#[doc = "Register `LP_INT_ENA` reader"]
pub type R = crate::R<LP_INT_ENA_SPEC>;
#[doc = "Register `LP_INT_ENA` writer"]
pub type W = crate::W<LP_INT_ENA_SPEC>;
#[doc = "Field `LP_CPU_WAKEUP` reader - need_des"]
pub type LP_CPU_WAKEUP_R = crate::BitReader;
#[doc = "Field `LP_CPU_WAKEUP` writer - need_des"]
pub type LP_CPU_WAKEUP_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MODEM_SWITCH_ACTIVE_END` reader - need_des"]
pub type MODEM_SWITCH_ACTIVE_END_R = crate::BitReader;
#[doc = "Field `MODEM_SWITCH_ACTIVE_END` writer - need_des"]
pub type MODEM_SWITCH_ACTIVE_END_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLEEP_SWITCH_ACTIVE_END` reader - need_des"]
pub type SLEEP_SWITCH_ACTIVE_END_R = crate::BitReader;
#[doc = "Field `SLEEP_SWITCH_ACTIVE_END` writer - need_des"]
pub type SLEEP_SWITCH_ACTIVE_END_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLEEP_SWITCH_MODEM_END` reader - need_des"]
pub type SLEEP_SWITCH_MODEM_END_R = crate::BitReader;
#[doc = "Field `SLEEP_SWITCH_MODEM_END` writer - need_des"]
pub type SLEEP_SWITCH_MODEM_END_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MODEM_SWITCH_SLEEP_END` reader - need_des"]
pub type MODEM_SWITCH_SLEEP_END_R = crate::BitReader;
#[doc = "Field `MODEM_SWITCH_SLEEP_END` writer - need_des"]
pub type MODEM_SWITCH_SLEEP_END_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ACTIVE_SWITCH_SLEEP_END` reader - need_des"]
pub type ACTIVE_SWITCH_SLEEP_END_R = crate::BitReader;
#[doc = "Field `ACTIVE_SWITCH_SLEEP_END` writer - need_des"]
pub type ACTIVE_SWITCH_SLEEP_END_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MODEM_SWITCH_ACTIVE_START` reader - need_des"]
pub type MODEM_SWITCH_ACTIVE_START_R = crate::BitReader;
#[doc = "Field `MODEM_SWITCH_ACTIVE_START` writer - need_des"]
pub type MODEM_SWITCH_ACTIVE_START_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLEEP_SWITCH_ACTIVE_START` reader - need_des"]
pub type SLEEP_SWITCH_ACTIVE_START_R = crate::BitReader;
#[doc = "Field `SLEEP_SWITCH_ACTIVE_START` writer - need_des"]
pub type SLEEP_SWITCH_ACTIVE_START_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLEEP_SWITCH_MODEM_START` reader - need_des"]
pub type SLEEP_SWITCH_MODEM_START_R = crate::BitReader;
#[doc = "Field `SLEEP_SWITCH_MODEM_START` writer - need_des"]
pub type SLEEP_SWITCH_MODEM_START_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MODEM_SWITCH_SLEEP_START` reader - need_des"]
pub type MODEM_SWITCH_SLEEP_START_R = crate::BitReader;
#[doc = "Field `MODEM_SWITCH_SLEEP_START` writer - need_des"]
pub type MODEM_SWITCH_SLEEP_START_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ACTIVE_SWITCH_SLEEP_START` reader - need_des"]
pub type ACTIVE_SWITCH_SLEEP_START_R = crate::BitReader;
#[doc = "Field `ACTIVE_SWITCH_SLEEP_START` writer - need_des"]
pub type ACTIVE_SWITCH_SLEEP_START_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HP_SW_TRIGGER` reader - need_des"]
pub type HP_SW_TRIGGER_R = crate::BitReader;
#[doc = "Field `HP_SW_TRIGGER` writer - need_des"]
pub type HP_SW_TRIGGER_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 20 - need_des"]
    #[inline(always)]
    pub fn lp_cpu_wakeup(&self) -> LP_CPU_WAKEUP_R {
        LP_CPU_WAKEUP_R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - need_des"]
    #[inline(always)]
    pub fn modem_switch_active_end(&self) -> MODEM_SWITCH_ACTIVE_END_R {
        MODEM_SWITCH_ACTIVE_END_R::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 22 - need_des"]
    #[inline(always)]
    pub fn sleep_switch_active_end(&self) -> SLEEP_SWITCH_ACTIVE_END_R {
        SLEEP_SWITCH_ACTIVE_END_R::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 23 - need_des"]
    #[inline(always)]
    pub fn sleep_switch_modem_end(&self) -> SLEEP_SWITCH_MODEM_END_R {
        SLEEP_SWITCH_MODEM_END_R::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bit 24 - need_des"]
    #[inline(always)]
    pub fn modem_switch_sleep_end(&self) -> MODEM_SWITCH_SLEEP_END_R {
        MODEM_SWITCH_SLEEP_END_R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - need_des"]
    #[inline(always)]
    pub fn active_switch_sleep_end(&self) -> ACTIVE_SWITCH_SLEEP_END_R {
        ACTIVE_SWITCH_SLEEP_END_R::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - need_des"]
    #[inline(always)]
    pub fn modem_switch_active_start(&self) -> MODEM_SWITCH_ACTIVE_START_R {
        MODEM_SWITCH_ACTIVE_START_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - need_des"]
    #[inline(always)]
    pub fn sleep_switch_active_start(&self) -> SLEEP_SWITCH_ACTIVE_START_R {
        SLEEP_SWITCH_ACTIVE_START_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - need_des"]
    #[inline(always)]
    pub fn sleep_switch_modem_start(&self) -> SLEEP_SWITCH_MODEM_START_R {
        SLEEP_SWITCH_MODEM_START_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn modem_switch_sleep_start(&self) -> MODEM_SWITCH_SLEEP_START_R {
        MODEM_SWITCH_SLEEP_START_R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn active_switch_sleep_start(&self) -> ACTIVE_SWITCH_SLEEP_START_R {
        ACTIVE_SWITCH_SLEEP_START_R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn hp_sw_trigger(&self) -> HP_SW_TRIGGER_R {
        HP_SW_TRIGGER_R::new(((self.bits >> 31) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("LP_INT_ENA")
            .field("lp_cpu_wakeup", &self.lp_cpu_wakeup())
            .field("modem_switch_active_end", &self.modem_switch_active_end())
            .field("sleep_switch_active_end", &self.sleep_switch_active_end())
            .field("sleep_switch_modem_end", &self.sleep_switch_modem_end())
            .field("modem_switch_sleep_end", &self.modem_switch_sleep_end())
            .field("active_switch_sleep_end", &self.active_switch_sleep_end())
            .field(
                "modem_switch_active_start",
                &self.modem_switch_active_start(),
            )
            .field(
                "sleep_switch_active_start",
                &self.sleep_switch_active_start(),
            )
            .field("sleep_switch_modem_start", &self.sleep_switch_modem_start())
            .field("modem_switch_sleep_start", &self.modem_switch_sleep_start())
            .field(
                "active_switch_sleep_start",
                &self.active_switch_sleep_start(),
            )
            .field("hp_sw_trigger", &self.hp_sw_trigger())
            .finish()
    }
}
impl W {
    #[doc = "Bit 20 - need_des"]
    #[inline(always)]
    pub fn lp_cpu_wakeup(&mut self) -> LP_CPU_WAKEUP_W<'_, LP_INT_ENA_SPEC> {
        LP_CPU_WAKEUP_W::new(self, 20)
    }
    #[doc = "Bit 21 - need_des"]
    #[inline(always)]
    pub fn modem_switch_active_end(&mut self) -> MODEM_SWITCH_ACTIVE_END_W<'_, LP_INT_ENA_SPEC> {
        MODEM_SWITCH_ACTIVE_END_W::new(self, 21)
    }
    #[doc = "Bit 22 - need_des"]
    #[inline(always)]
    pub fn sleep_switch_active_end(&mut self) -> SLEEP_SWITCH_ACTIVE_END_W<'_, LP_INT_ENA_SPEC> {
        SLEEP_SWITCH_ACTIVE_END_W::new(self, 22)
    }
    #[doc = "Bit 23 - need_des"]
    #[inline(always)]
    pub fn sleep_switch_modem_end(&mut self) -> SLEEP_SWITCH_MODEM_END_W<'_, LP_INT_ENA_SPEC> {
        SLEEP_SWITCH_MODEM_END_W::new(self, 23)
    }
    #[doc = "Bit 24 - need_des"]
    #[inline(always)]
    pub fn modem_switch_sleep_end(&mut self) -> MODEM_SWITCH_SLEEP_END_W<'_, LP_INT_ENA_SPEC> {
        MODEM_SWITCH_SLEEP_END_W::new(self, 24)
    }
    #[doc = "Bit 25 - need_des"]
    #[inline(always)]
    pub fn active_switch_sleep_end(&mut self) -> ACTIVE_SWITCH_SLEEP_END_W<'_, LP_INT_ENA_SPEC> {
        ACTIVE_SWITCH_SLEEP_END_W::new(self, 25)
    }
    #[doc = "Bit 26 - need_des"]
    #[inline(always)]
    pub fn modem_switch_active_start(
        &mut self,
    ) -> MODEM_SWITCH_ACTIVE_START_W<'_, LP_INT_ENA_SPEC> {
        MODEM_SWITCH_ACTIVE_START_W::new(self, 26)
    }
    #[doc = "Bit 27 - need_des"]
    #[inline(always)]
    pub fn sleep_switch_active_start(
        &mut self,
    ) -> SLEEP_SWITCH_ACTIVE_START_W<'_, LP_INT_ENA_SPEC> {
        SLEEP_SWITCH_ACTIVE_START_W::new(self, 27)
    }
    #[doc = "Bit 28 - need_des"]
    #[inline(always)]
    pub fn sleep_switch_modem_start(&mut self) -> SLEEP_SWITCH_MODEM_START_W<'_, LP_INT_ENA_SPEC> {
        SLEEP_SWITCH_MODEM_START_W::new(self, 28)
    }
    #[doc = "Bit 29 - need_des"]
    #[inline(always)]
    pub fn modem_switch_sleep_start(&mut self) -> MODEM_SWITCH_SLEEP_START_W<'_, LP_INT_ENA_SPEC> {
        MODEM_SWITCH_SLEEP_START_W::new(self, 29)
    }
    #[doc = "Bit 30 - need_des"]
    #[inline(always)]
    pub fn active_switch_sleep_start(
        &mut self,
    ) -> ACTIVE_SWITCH_SLEEP_START_W<'_, LP_INT_ENA_SPEC> {
        ACTIVE_SWITCH_SLEEP_START_W::new(self, 30)
    }
    #[doc = "Bit 31 - need_des"]
    #[inline(always)]
    pub fn hp_sw_trigger(&mut self) -> HP_SW_TRIGGER_W<'_, LP_INT_ENA_SPEC> {
        HP_SW_TRIGGER_W::new(self, 31)
    }
}
#[doc = "need_des\n\nYou can [`read`](crate::Reg::read) this register and get [`lp_int_ena::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`lp_int_ena::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LP_INT_ENA_SPEC;
impl crate::RegisterSpec for LP_INT_ENA_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`lp_int_ena::R`](R) reader structure"]
impl crate::Readable for LP_INT_ENA_SPEC {}
#[doc = "`write(|w| ..)` method takes [`lp_int_ena::W`](W) writer structure"]
impl crate::Writable for LP_INT_ENA_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets LP_INT_ENA to value 0"]
impl crate::Resettable for LP_INT_ENA_SPEC {}
