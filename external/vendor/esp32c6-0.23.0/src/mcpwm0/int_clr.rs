#[doc = "Register `INT_CLR` writer"]
pub type W = crate::W<INT_CLR_SPEC>;
#[doc = "Field `TIMER0_STOP` writer - Set this bit to clear the interrupt triggered when the timer 0 stops."]
pub type TIMER0_STOP_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `TIMER1_STOP` writer - Set this bit to clear the interrupt triggered when the timer 1 stops."]
pub type TIMER1_STOP_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `TIMER2_STOP` writer - Set this bit to clear the interrupt triggered when the timer 2 stops."]
pub type TIMER2_STOP_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `TIMER0_TEZ` writer - Set this bit to clear the interrupt triggered by a PWM timer 0 TEZ event."]
pub type TIMER0_TEZ_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `TIMER1_TEZ` writer - Set this bit to clear the interrupt triggered by a PWM timer 1 TEZ event."]
pub type TIMER1_TEZ_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `TIMER2_TEZ` writer - Set this bit to clear the interrupt triggered by a PWM timer 2 TEZ event."]
pub type TIMER2_TEZ_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `TIMER0_TEP` writer - Set this bit to clear the interrupt triggered by a PWM timer 0 TEP event."]
pub type TIMER0_TEP_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `TIMER1_TEP` writer - Set this bit to clear the interrupt triggered by a PWM timer 1 TEP event."]
pub type TIMER1_TEP_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `TIMER2_TEP` writer - Set this bit to clear the interrupt triggered by a PWM timer 2 TEP event."]
pub type TIMER2_TEP_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `FAULT0` writer - Set this bit to clear the interrupt triggered when event_f0 starts."]
pub type FAULT0_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `FAULT1` writer - Set this bit to clear the interrupt triggered when event_f1 starts."]
pub type FAULT1_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `FAULT2` writer - Set this bit to clear the interrupt triggered when event_f2 starts."]
pub type FAULT2_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `FAULT0_CLR` writer - Set this bit to clear the interrupt triggered when event_f0 ends."]
pub type FAULT0_CLR_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `FAULT1_CLR` writer - Set this bit to clear the interrupt triggered when event_f1 ends."]
pub type FAULT1_CLR_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `FAULT2_CLR` writer - Set this bit to clear the interrupt triggered when event_f2 ends."]
pub type FAULT2_CLR_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `CMPR0_TEA` writer - Set this bit to clear the interrupt triggered by a PWM operator 0 TEA event"]
pub type CMPR0_TEA_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `CMPR1_TEA` writer - Set this bit to clear the interrupt triggered by a PWM operator 1 TEA event"]
pub type CMPR1_TEA_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `CMPR2_TEA` writer - Set this bit to clear the interrupt triggered by a PWM operator 2 TEA event"]
pub type CMPR2_TEA_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `CMPR0_TEB` writer - Set this bit to clear the interrupt triggered by a PWM operator 0 TEB event"]
pub type CMPR0_TEB_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `CMPR1_TEB` writer - Set this bit to clear the interrupt triggered by a PWM operator 1 TEB event"]
pub type CMPR1_TEB_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `CMPR2_TEB` writer - Set this bit to clear the interrupt triggered by a PWM operator 2 TEB event"]
pub type CMPR2_TEB_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `TZ0_CBC` writer - Set this bit to clear the interrupt triggered by a cycle-by-cycle mode action on PWM0."]
pub type TZ0_CBC_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `TZ1_CBC` writer - Set this bit to clear the interrupt triggered by a cycle-by-cycle mode action on PWM1."]
pub type TZ1_CBC_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `TZ2_CBC` writer - Set this bit to clear the interrupt triggered by a cycle-by-cycle mode action on PWM2."]
pub type TZ2_CBC_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `TZ0_OST` writer - Set this bit to clear the interrupt triggered by a one-shot mode action on PWM0."]
pub type TZ0_OST_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `TZ1_OST` writer - Set this bit to clear the interrupt triggered by a one-shot mode action on PWM1."]
pub type TZ1_OST_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `TZ2_OST` writer - Set this bit to clear the interrupt triggered by a one-shot mode action on PWM2."]
pub type TZ2_OST_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `CAP0` writer - Set this bit to clear the interrupt triggered by capture on channel 0."]
pub type CAP0_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `CAP1` writer - Set this bit to clear the interrupt triggered by capture on channel 1."]
pub type CAP1_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[doc = "Field `CAP2` writer - Set this bit to clear the interrupt triggered by capture on channel 2."]
pub type CAP2_W<'a, REG> = crate::BitWriter1C<'a, REG>;
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for crate::generic::Reg<INT_CLR_SPEC> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "(not readable)")
    }
}
impl W {
    #[doc = "Bit 0 - Set this bit to clear the interrupt triggered when the timer 0 stops."]
    #[inline(always)]
    pub fn timer0_stop(&mut self) -> TIMER0_STOP_W<'_, INT_CLR_SPEC> {
        TIMER0_STOP_W::new(self, 0)
    }
    #[doc = "Bit 1 - Set this bit to clear the interrupt triggered when the timer 1 stops."]
    #[inline(always)]
    pub fn timer1_stop(&mut self) -> TIMER1_STOP_W<'_, INT_CLR_SPEC> {
        TIMER1_STOP_W::new(self, 1)
    }
    #[doc = "Bit 2 - Set this bit to clear the interrupt triggered when the timer 2 stops."]
    #[inline(always)]
    pub fn timer2_stop(&mut self) -> TIMER2_STOP_W<'_, INT_CLR_SPEC> {
        TIMER2_STOP_W::new(self, 2)
    }
    #[doc = "Bit 3 - Set this bit to clear the interrupt triggered by a PWM timer 0 TEZ event."]
    #[inline(always)]
    pub fn timer0_tez(&mut self) -> TIMER0_TEZ_W<'_, INT_CLR_SPEC> {
        TIMER0_TEZ_W::new(self, 3)
    }
    #[doc = "Bit 4 - Set this bit to clear the interrupt triggered by a PWM timer 1 TEZ event."]
    #[inline(always)]
    pub fn timer1_tez(&mut self) -> TIMER1_TEZ_W<'_, INT_CLR_SPEC> {
        TIMER1_TEZ_W::new(self, 4)
    }
    #[doc = "Bit 5 - Set this bit to clear the interrupt triggered by a PWM timer 2 TEZ event."]
    #[inline(always)]
    pub fn timer2_tez(&mut self) -> TIMER2_TEZ_W<'_, INT_CLR_SPEC> {
        TIMER2_TEZ_W::new(self, 5)
    }
    #[doc = "Bit 6 - Set this bit to clear the interrupt triggered by a PWM timer 0 TEP event."]
    #[inline(always)]
    pub fn timer0_tep(&mut self) -> TIMER0_TEP_W<'_, INT_CLR_SPEC> {
        TIMER0_TEP_W::new(self, 6)
    }
    #[doc = "Bit 7 - Set this bit to clear the interrupt triggered by a PWM timer 1 TEP event."]
    #[inline(always)]
    pub fn timer1_tep(&mut self) -> TIMER1_TEP_W<'_, INT_CLR_SPEC> {
        TIMER1_TEP_W::new(self, 7)
    }
    #[doc = "Bit 8 - Set this bit to clear the interrupt triggered by a PWM timer 2 TEP event."]
    #[inline(always)]
    pub fn timer2_tep(&mut self) -> TIMER2_TEP_W<'_, INT_CLR_SPEC> {
        TIMER2_TEP_W::new(self, 8)
    }
    #[doc = "Bit 9 - Set this bit to clear the interrupt triggered when event_f0 starts."]
    #[inline(always)]
    pub fn fault0(&mut self) -> FAULT0_W<'_, INT_CLR_SPEC> {
        FAULT0_W::new(self, 9)
    }
    #[doc = "Bit 10 - Set this bit to clear the interrupt triggered when event_f1 starts."]
    #[inline(always)]
    pub fn fault1(&mut self) -> FAULT1_W<'_, INT_CLR_SPEC> {
        FAULT1_W::new(self, 10)
    }
    #[doc = "Bit 11 - Set this bit to clear the interrupt triggered when event_f2 starts."]
    #[inline(always)]
    pub fn fault2(&mut self) -> FAULT2_W<'_, INT_CLR_SPEC> {
        FAULT2_W::new(self, 11)
    }
    #[doc = "Bit 12 - Set this bit to clear the interrupt triggered when event_f0 ends."]
    #[inline(always)]
    pub fn fault0_clr(&mut self) -> FAULT0_CLR_W<'_, INT_CLR_SPEC> {
        FAULT0_CLR_W::new(self, 12)
    }
    #[doc = "Bit 13 - Set this bit to clear the interrupt triggered when event_f1 ends."]
    #[inline(always)]
    pub fn fault1_clr(&mut self) -> FAULT1_CLR_W<'_, INT_CLR_SPEC> {
        FAULT1_CLR_W::new(self, 13)
    }
    #[doc = "Bit 14 - Set this bit to clear the interrupt triggered when event_f2 ends."]
    #[inline(always)]
    pub fn fault2_clr(&mut self) -> FAULT2_CLR_W<'_, INT_CLR_SPEC> {
        FAULT2_CLR_W::new(self, 14)
    }
    #[doc = "Bit 15 - Set this bit to clear the interrupt triggered by a PWM operator 0 TEA event"]
    #[inline(always)]
    pub fn cmpr0_tea(&mut self) -> CMPR0_TEA_W<'_, INT_CLR_SPEC> {
        CMPR0_TEA_W::new(self, 15)
    }
    #[doc = "Bit 16 - Set this bit to clear the interrupt triggered by a PWM operator 1 TEA event"]
    #[inline(always)]
    pub fn cmpr1_tea(&mut self) -> CMPR1_TEA_W<'_, INT_CLR_SPEC> {
        CMPR1_TEA_W::new(self, 16)
    }
    #[doc = "Bit 17 - Set this bit to clear the interrupt triggered by a PWM operator 2 TEA event"]
    #[inline(always)]
    pub fn cmpr2_tea(&mut self) -> CMPR2_TEA_W<'_, INT_CLR_SPEC> {
        CMPR2_TEA_W::new(self, 17)
    }
    #[doc = "Bit 18 - Set this bit to clear the interrupt triggered by a PWM operator 0 TEB event"]
    #[inline(always)]
    pub fn cmpr0_teb(&mut self) -> CMPR0_TEB_W<'_, INT_CLR_SPEC> {
        CMPR0_TEB_W::new(self, 18)
    }
    #[doc = "Bit 19 - Set this bit to clear the interrupt triggered by a PWM operator 1 TEB event"]
    #[inline(always)]
    pub fn cmpr1_teb(&mut self) -> CMPR1_TEB_W<'_, INT_CLR_SPEC> {
        CMPR1_TEB_W::new(self, 19)
    }
    #[doc = "Bit 20 - Set this bit to clear the interrupt triggered by a PWM operator 2 TEB event"]
    #[inline(always)]
    pub fn cmpr2_teb(&mut self) -> CMPR2_TEB_W<'_, INT_CLR_SPEC> {
        CMPR2_TEB_W::new(self, 20)
    }
    #[doc = "Bit 21 - Set this bit to clear the interrupt triggered by a cycle-by-cycle mode action on PWM0."]
    #[inline(always)]
    pub fn tz0_cbc(&mut self) -> TZ0_CBC_W<'_, INT_CLR_SPEC> {
        TZ0_CBC_W::new(self, 21)
    }
    #[doc = "Bit 22 - Set this bit to clear the interrupt triggered by a cycle-by-cycle mode action on PWM1."]
    #[inline(always)]
    pub fn tz1_cbc(&mut self) -> TZ1_CBC_W<'_, INT_CLR_SPEC> {
        TZ1_CBC_W::new(self, 22)
    }
    #[doc = "Bit 23 - Set this bit to clear the interrupt triggered by a cycle-by-cycle mode action on PWM2."]
    #[inline(always)]
    pub fn tz2_cbc(&mut self) -> TZ2_CBC_W<'_, INT_CLR_SPEC> {
        TZ2_CBC_W::new(self, 23)
    }
    #[doc = "Bit 24 - Set this bit to clear the interrupt triggered by a one-shot mode action on PWM0."]
    #[inline(always)]
    pub fn tz0_ost(&mut self) -> TZ0_OST_W<'_, INT_CLR_SPEC> {
        TZ0_OST_W::new(self, 24)
    }
    #[doc = "Bit 25 - Set this bit to clear the interrupt triggered by a one-shot mode action on PWM1."]
    #[inline(always)]
    pub fn tz1_ost(&mut self) -> TZ1_OST_W<'_, INT_CLR_SPEC> {
        TZ1_OST_W::new(self, 25)
    }
    #[doc = "Bit 26 - Set this bit to clear the interrupt triggered by a one-shot mode action on PWM2."]
    #[inline(always)]
    pub fn tz2_ost(&mut self) -> TZ2_OST_W<'_, INT_CLR_SPEC> {
        TZ2_OST_W::new(self, 26)
    }
    #[doc = "Bit 27 - Set this bit to clear the interrupt triggered by capture on channel 0."]
    #[inline(always)]
    pub fn cap0(&mut self) -> CAP0_W<'_, INT_CLR_SPEC> {
        CAP0_W::new(self, 27)
    }
    #[doc = "Bit 28 - Set this bit to clear the interrupt triggered by capture on channel 1."]
    #[inline(always)]
    pub fn cap1(&mut self) -> CAP1_W<'_, INT_CLR_SPEC> {
        CAP1_W::new(self, 28)
    }
    #[doc = "Bit 29 - Set this bit to clear the interrupt triggered by capture on channel 2."]
    #[inline(always)]
    pub fn cap2(&mut self) -> CAP2_W<'_, INT_CLR_SPEC> {
        CAP2_W::new(self, 29)
    }
}
#[doc = "Interrupt clear bits\n\nYou can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_clr::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INT_CLR_SPEC;
impl crate::RegisterSpec for INT_CLR_SPEC {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`int_clr::W`](W) writer structure"]
impl crate::Writable for INT_CLR_SPEC {
    type Safety = crate::Unsafe;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0x3fff_ffff;
}
#[doc = "`reset()` method sets INT_CLR to value 0"]
impl crate::Resettable for INT_CLR_SPEC {}
