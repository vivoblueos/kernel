#[doc = "Register `INT_ENA` reader"]
pub type R = crate::R<INT_ENA_SPEC>;
#[doc = "Register `INT_ENA` writer"]
pub type W = crate::W<INT_ENA_SPEC>;
#[doc = "Field `TIMER0_STOP` reader - The enable bit for the interrupt triggered when the timer 0 stops."]
pub type TIMER0_STOP_R = crate::BitReader;
#[doc = "Field `TIMER0_STOP` writer - The enable bit for the interrupt triggered when the timer 0 stops."]
pub type TIMER0_STOP_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER1_STOP` reader - The enable bit for the interrupt triggered when the timer 1 stops."]
pub type TIMER1_STOP_R = crate::BitReader;
#[doc = "Field `TIMER1_STOP` writer - The enable bit for the interrupt triggered when the timer 1 stops."]
pub type TIMER1_STOP_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER2_STOP` reader - The enable bit for the interrupt triggered when the timer 2 stops."]
pub type TIMER2_STOP_R = crate::BitReader;
#[doc = "Field `TIMER2_STOP` writer - The enable bit for the interrupt triggered when the timer 2 stops."]
pub type TIMER2_STOP_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER0_TEZ` reader - The enable bit for the interrupt triggered by a PWM timer 0 TEZ event."]
pub type TIMER0_TEZ_R = crate::BitReader;
#[doc = "Field `TIMER0_TEZ` writer - The enable bit for the interrupt triggered by a PWM timer 0 TEZ event."]
pub type TIMER0_TEZ_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER1_TEZ` reader - The enable bit for the interrupt triggered by a PWM timer 1 TEZ event."]
pub type TIMER1_TEZ_R = crate::BitReader;
#[doc = "Field `TIMER1_TEZ` writer - The enable bit for the interrupt triggered by a PWM timer 1 TEZ event."]
pub type TIMER1_TEZ_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER2_TEZ` reader - The enable bit for the interrupt triggered by a PWM timer 2 TEZ event."]
pub type TIMER2_TEZ_R = crate::BitReader;
#[doc = "Field `TIMER2_TEZ` writer - The enable bit for the interrupt triggered by a PWM timer 2 TEZ event."]
pub type TIMER2_TEZ_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER0_TEP` reader - The enable bit for the interrupt triggered by a PWM timer 0 TEP event."]
pub type TIMER0_TEP_R = crate::BitReader;
#[doc = "Field `TIMER0_TEP` writer - The enable bit for the interrupt triggered by a PWM timer 0 TEP event."]
pub type TIMER0_TEP_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER1_TEP` reader - The enable bit for the interrupt triggered by a PWM timer 1 TEP event."]
pub type TIMER1_TEP_R = crate::BitReader;
#[doc = "Field `TIMER1_TEP` writer - The enable bit for the interrupt triggered by a PWM timer 1 TEP event."]
pub type TIMER1_TEP_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER2_TEP` reader - The enable bit for the interrupt triggered by a PWM timer 2 TEP event."]
pub type TIMER2_TEP_R = crate::BitReader;
#[doc = "Field `TIMER2_TEP` writer - The enable bit for the interrupt triggered by a PWM timer 2 TEP event."]
pub type TIMER2_TEP_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FAULT0` reader - The enable bit for the interrupt triggered when event_f0 starts."]
pub type FAULT0_R = crate::BitReader;
#[doc = "Field `FAULT0` writer - The enable bit for the interrupt triggered when event_f0 starts."]
pub type FAULT0_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FAULT1` reader - The enable bit for the interrupt triggered when event_f1 starts."]
pub type FAULT1_R = crate::BitReader;
#[doc = "Field `FAULT1` writer - The enable bit for the interrupt triggered when event_f1 starts."]
pub type FAULT1_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FAULT2` reader - The enable bit for the interrupt triggered when event_f2 starts."]
pub type FAULT2_R = crate::BitReader;
#[doc = "Field `FAULT2` writer - The enable bit for the interrupt triggered when event_f2 starts."]
pub type FAULT2_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FAULT0_CLR` reader - The enable bit for the interrupt triggered when event_f0 ends."]
pub type FAULT0_CLR_R = crate::BitReader;
#[doc = "Field `FAULT0_CLR` writer - The enable bit for the interrupt triggered when event_f0 ends."]
pub type FAULT0_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FAULT1_CLR` reader - The enable bit for the interrupt triggered when event_f1 ends."]
pub type FAULT1_CLR_R = crate::BitReader;
#[doc = "Field `FAULT1_CLR` writer - The enable bit for the interrupt triggered when event_f1 ends."]
pub type FAULT1_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FAULT2_CLR` reader - The enable bit for the interrupt triggered when event_f2 ends."]
pub type FAULT2_CLR_R = crate::BitReader;
#[doc = "Field `FAULT2_CLR` writer - The enable bit for the interrupt triggered when event_f2 ends."]
pub type FAULT2_CLR_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMPR0_TEA` reader - The enable bit for the interrupt triggered by a PWM operator 0 TEA event"]
pub type CMPR0_TEA_R = crate::BitReader;
#[doc = "Field `CMPR0_TEA` writer - The enable bit for the interrupt triggered by a PWM operator 0 TEA event"]
pub type CMPR0_TEA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMPR1_TEA` reader - The enable bit for the interrupt triggered by a PWM operator 1 TEA event"]
pub type CMPR1_TEA_R = crate::BitReader;
#[doc = "Field `CMPR1_TEA` writer - The enable bit for the interrupt triggered by a PWM operator 1 TEA event"]
pub type CMPR1_TEA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMPR2_TEA` reader - The enable bit for the interrupt triggered by a PWM operator 2 TEA event"]
pub type CMPR2_TEA_R = crate::BitReader;
#[doc = "Field `CMPR2_TEA` writer - The enable bit for the interrupt triggered by a PWM operator 2 TEA event"]
pub type CMPR2_TEA_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMPR0_TEB` reader - The enable bit for the interrupt triggered by a PWM operator 0 TEB event"]
pub type CMPR0_TEB_R = crate::BitReader;
#[doc = "Field `CMPR0_TEB` writer - The enable bit for the interrupt triggered by a PWM operator 0 TEB event"]
pub type CMPR0_TEB_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMPR1_TEB` reader - The enable bit for the interrupt triggered by a PWM operator 1 TEB event"]
pub type CMPR1_TEB_R = crate::BitReader;
#[doc = "Field `CMPR1_TEB` writer - The enable bit for the interrupt triggered by a PWM operator 1 TEB event"]
pub type CMPR1_TEB_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMPR2_TEB` reader - The enable bit for the interrupt triggered by a PWM operator 2 TEB event"]
pub type CMPR2_TEB_R = crate::BitReader;
#[doc = "Field `CMPR2_TEB` writer - The enable bit for the interrupt triggered by a PWM operator 2 TEB event"]
pub type CMPR2_TEB_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TZ0_CBC` reader - The enable bit for the interrupt triggered by a cycle-by-cycle mode action on PWM0."]
pub type TZ0_CBC_R = crate::BitReader;
#[doc = "Field `TZ0_CBC` writer - The enable bit for the interrupt triggered by a cycle-by-cycle mode action on PWM0."]
pub type TZ0_CBC_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TZ1_CBC` reader - The enable bit for the interrupt triggered by a cycle-by-cycle mode action on PWM1."]
pub type TZ1_CBC_R = crate::BitReader;
#[doc = "Field `TZ1_CBC` writer - The enable bit for the interrupt triggered by a cycle-by-cycle mode action on PWM1."]
pub type TZ1_CBC_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TZ2_CBC` reader - The enable bit for the interrupt triggered by a cycle-by-cycle mode action on PWM2."]
pub type TZ2_CBC_R = crate::BitReader;
#[doc = "Field `TZ2_CBC` writer - The enable bit for the interrupt triggered by a cycle-by-cycle mode action on PWM2."]
pub type TZ2_CBC_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TZ0_OST` reader - The enable bit for the interrupt triggered by a one-shot mode action on PWM0."]
pub type TZ0_OST_R = crate::BitReader;
#[doc = "Field `TZ0_OST` writer - The enable bit for the interrupt triggered by a one-shot mode action on PWM0."]
pub type TZ0_OST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TZ1_OST` reader - The enable bit for the interrupt triggered by a one-shot mode action on PWM1."]
pub type TZ1_OST_R = crate::BitReader;
#[doc = "Field `TZ1_OST` writer - The enable bit for the interrupt triggered by a one-shot mode action on PWM1."]
pub type TZ1_OST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TZ2_OST` reader - The enable bit for the interrupt triggered by a one-shot mode action on PWM2."]
pub type TZ2_OST_R = crate::BitReader;
#[doc = "Field `TZ2_OST` writer - The enable bit for the interrupt triggered by a one-shot mode action on PWM2."]
pub type TZ2_OST_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CAP0` reader - The enable bit for the interrupt triggered by capture on channel 0."]
pub type CAP0_R = crate::BitReader;
#[doc = "Field `CAP0` writer - The enable bit for the interrupt triggered by capture on channel 0."]
pub type CAP0_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CAP1` reader - The enable bit for the interrupt triggered by capture on channel 1."]
pub type CAP1_R = crate::BitReader;
#[doc = "Field `CAP1` writer - The enable bit for the interrupt triggered by capture on channel 1."]
pub type CAP1_W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CAP2` reader - The enable bit for the interrupt triggered by capture on channel 2."]
pub type CAP2_R = crate::BitReader;
#[doc = "Field `CAP2` writer - The enable bit for the interrupt triggered by capture on channel 2."]
pub type CAP2_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - The enable bit for the interrupt triggered when the timer 0 stops."]
    #[inline(always)]
    pub fn timer0_stop(&self) -> TIMER0_STOP_R {
        TIMER0_STOP_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The enable bit for the interrupt triggered when the timer 1 stops."]
    #[inline(always)]
    pub fn timer1_stop(&self) -> TIMER1_STOP_R {
        TIMER1_STOP_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - The enable bit for the interrupt triggered when the timer 2 stops."]
    #[inline(always)]
    pub fn timer2_stop(&self) -> TIMER2_STOP_R {
        TIMER2_STOP_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - The enable bit for the interrupt triggered by a PWM timer 0 TEZ event."]
    #[inline(always)]
    pub fn timer0_tez(&self) -> TIMER0_TEZ_R {
        TIMER0_TEZ_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - The enable bit for the interrupt triggered by a PWM timer 1 TEZ event."]
    #[inline(always)]
    pub fn timer1_tez(&self) -> TIMER1_TEZ_R {
        TIMER1_TEZ_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - The enable bit for the interrupt triggered by a PWM timer 2 TEZ event."]
    #[inline(always)]
    pub fn timer2_tez(&self) -> TIMER2_TEZ_R {
        TIMER2_TEZ_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - The enable bit for the interrupt triggered by a PWM timer 0 TEP event."]
    #[inline(always)]
    pub fn timer0_tep(&self) -> TIMER0_TEP_R {
        TIMER0_TEP_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - The enable bit for the interrupt triggered by a PWM timer 1 TEP event."]
    #[inline(always)]
    pub fn timer1_tep(&self) -> TIMER1_TEP_R {
        TIMER1_TEP_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - The enable bit for the interrupt triggered by a PWM timer 2 TEP event."]
    #[inline(always)]
    pub fn timer2_tep(&self) -> TIMER2_TEP_R {
        TIMER2_TEP_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - The enable bit for the interrupt triggered when event_f0 starts."]
    #[inline(always)]
    pub fn fault0(&self) -> FAULT0_R {
        FAULT0_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - The enable bit for the interrupt triggered when event_f1 starts."]
    #[inline(always)]
    pub fn fault1(&self) -> FAULT1_R {
        FAULT1_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - The enable bit for the interrupt triggered when event_f2 starts."]
    #[inline(always)]
    pub fn fault2(&self) -> FAULT2_R {
        FAULT2_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - The enable bit for the interrupt triggered when event_f0 ends."]
    #[inline(always)]
    pub fn fault0_clr(&self) -> FAULT0_CLR_R {
        FAULT0_CLR_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - The enable bit for the interrupt triggered when event_f1 ends."]
    #[inline(always)]
    pub fn fault1_clr(&self) -> FAULT1_CLR_R {
        FAULT1_CLR_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - The enable bit for the interrupt triggered when event_f2 ends."]
    #[inline(always)]
    pub fn fault2_clr(&self) -> FAULT2_CLR_R {
        FAULT2_CLR_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - The enable bit for the interrupt triggered by a PWM operator 0 TEA event"]
    #[inline(always)]
    pub fn cmpr0_tea(&self) -> CMPR0_TEA_R {
        CMPR0_TEA_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - The enable bit for the interrupt triggered by a PWM operator 1 TEA event"]
    #[inline(always)]
    pub fn cmpr1_tea(&self) -> CMPR1_TEA_R {
        CMPR1_TEA_R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - The enable bit for the interrupt triggered by a PWM operator 2 TEA event"]
    #[inline(always)]
    pub fn cmpr2_tea(&self) -> CMPR2_TEA_R {
        CMPR2_TEA_R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - The enable bit for the interrupt triggered by a PWM operator 0 TEB event"]
    #[inline(always)]
    pub fn cmpr0_teb(&self) -> CMPR0_TEB_R {
        CMPR0_TEB_R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - The enable bit for the interrupt triggered by a PWM operator 1 TEB event"]
    #[inline(always)]
    pub fn cmpr1_teb(&self) -> CMPR1_TEB_R {
        CMPR1_TEB_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - The enable bit for the interrupt triggered by a PWM operator 2 TEB event"]
    #[inline(always)]
    pub fn cmpr2_teb(&self) -> CMPR2_TEB_R {
        CMPR2_TEB_R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - The enable bit for the interrupt triggered by a cycle-by-cycle mode action on PWM0."]
    #[inline(always)]
    pub fn tz0_cbc(&self) -> TZ0_CBC_R {
        TZ0_CBC_R::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 22 - The enable bit for the interrupt triggered by a cycle-by-cycle mode action on PWM1."]
    #[inline(always)]
    pub fn tz1_cbc(&self) -> TZ1_CBC_R {
        TZ1_CBC_R::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 23 - The enable bit for the interrupt triggered by a cycle-by-cycle mode action on PWM2."]
    #[inline(always)]
    pub fn tz2_cbc(&self) -> TZ2_CBC_R {
        TZ2_CBC_R::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bit 24 - The enable bit for the interrupt triggered by a one-shot mode action on PWM0."]
    #[inline(always)]
    pub fn tz0_ost(&self) -> TZ0_OST_R {
        TZ0_OST_R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - The enable bit for the interrupt triggered by a one-shot mode action on PWM1."]
    #[inline(always)]
    pub fn tz1_ost(&self) -> TZ1_OST_R {
        TZ1_OST_R::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - The enable bit for the interrupt triggered by a one-shot mode action on PWM2."]
    #[inline(always)]
    pub fn tz2_ost(&self) -> TZ2_OST_R {
        TZ2_OST_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - The enable bit for the interrupt triggered by capture on channel 0."]
    #[inline(always)]
    pub fn cap0(&self) -> CAP0_R {
        CAP0_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - The enable bit for the interrupt triggered by capture on channel 1."]
    #[inline(always)]
    pub fn cap1(&self) -> CAP1_R {
        CAP1_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - The enable bit for the interrupt triggered by capture on channel 2."]
    #[inline(always)]
    pub fn cap2(&self) -> CAP2_R {
        CAP2_R::new(((self.bits >> 29) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INT_ENA")
            .field("timer0_stop", &self.timer0_stop())
            .field("timer1_stop", &self.timer1_stop())
            .field("timer2_stop", &self.timer2_stop())
            .field("timer0_tez", &self.timer0_tez())
            .field("timer1_tez", &self.timer1_tez())
            .field("timer2_tez", &self.timer2_tez())
            .field("timer0_tep", &self.timer0_tep())
            .field("timer1_tep", &self.timer1_tep())
            .field("timer2_tep", &self.timer2_tep())
            .field("fault0", &self.fault0())
            .field("fault1", &self.fault1())
            .field("fault2", &self.fault2())
            .field("fault0_clr", &self.fault0_clr())
            .field("fault1_clr", &self.fault1_clr())
            .field("fault2_clr", &self.fault2_clr())
            .field("cmpr0_tea", &self.cmpr0_tea())
            .field("cmpr1_tea", &self.cmpr1_tea())
            .field("cmpr2_tea", &self.cmpr2_tea())
            .field("cmpr0_teb", &self.cmpr0_teb())
            .field("cmpr1_teb", &self.cmpr1_teb())
            .field("cmpr2_teb", &self.cmpr2_teb())
            .field("tz0_cbc", &self.tz0_cbc())
            .field("tz1_cbc", &self.tz1_cbc())
            .field("tz2_cbc", &self.tz2_cbc())
            .field("tz0_ost", &self.tz0_ost())
            .field("tz1_ost", &self.tz1_ost())
            .field("tz2_ost", &self.tz2_ost())
            .field("cap0", &self.cap0())
            .field("cap1", &self.cap1())
            .field("cap2", &self.cap2())
            .finish()
    }
}
impl W {
    #[doc = "Bit 0 - The enable bit for the interrupt triggered when the timer 0 stops."]
    #[inline(always)]
    pub fn timer0_stop(&mut self) -> TIMER0_STOP_W<'_, INT_ENA_SPEC> {
        TIMER0_STOP_W::new(self, 0)
    }
    #[doc = "Bit 1 - The enable bit for the interrupt triggered when the timer 1 stops."]
    #[inline(always)]
    pub fn timer1_stop(&mut self) -> TIMER1_STOP_W<'_, INT_ENA_SPEC> {
        TIMER1_STOP_W::new(self, 1)
    }
    #[doc = "Bit 2 - The enable bit for the interrupt triggered when the timer 2 stops."]
    #[inline(always)]
    pub fn timer2_stop(&mut self) -> TIMER2_STOP_W<'_, INT_ENA_SPEC> {
        TIMER2_STOP_W::new(self, 2)
    }
    #[doc = "Bit 3 - The enable bit for the interrupt triggered by a PWM timer 0 TEZ event."]
    #[inline(always)]
    pub fn timer0_tez(&mut self) -> TIMER0_TEZ_W<'_, INT_ENA_SPEC> {
        TIMER0_TEZ_W::new(self, 3)
    }
    #[doc = "Bit 4 - The enable bit for the interrupt triggered by a PWM timer 1 TEZ event."]
    #[inline(always)]
    pub fn timer1_tez(&mut self) -> TIMER1_TEZ_W<'_, INT_ENA_SPEC> {
        TIMER1_TEZ_W::new(self, 4)
    }
    #[doc = "Bit 5 - The enable bit for the interrupt triggered by a PWM timer 2 TEZ event."]
    #[inline(always)]
    pub fn timer2_tez(&mut self) -> TIMER2_TEZ_W<'_, INT_ENA_SPEC> {
        TIMER2_TEZ_W::new(self, 5)
    }
    #[doc = "Bit 6 - The enable bit for the interrupt triggered by a PWM timer 0 TEP event."]
    #[inline(always)]
    pub fn timer0_tep(&mut self) -> TIMER0_TEP_W<'_, INT_ENA_SPEC> {
        TIMER0_TEP_W::new(self, 6)
    }
    #[doc = "Bit 7 - The enable bit for the interrupt triggered by a PWM timer 1 TEP event."]
    #[inline(always)]
    pub fn timer1_tep(&mut self) -> TIMER1_TEP_W<'_, INT_ENA_SPEC> {
        TIMER1_TEP_W::new(self, 7)
    }
    #[doc = "Bit 8 - The enable bit for the interrupt triggered by a PWM timer 2 TEP event."]
    #[inline(always)]
    pub fn timer2_tep(&mut self) -> TIMER2_TEP_W<'_, INT_ENA_SPEC> {
        TIMER2_TEP_W::new(self, 8)
    }
    #[doc = "Bit 9 - The enable bit for the interrupt triggered when event_f0 starts."]
    #[inline(always)]
    pub fn fault0(&mut self) -> FAULT0_W<'_, INT_ENA_SPEC> {
        FAULT0_W::new(self, 9)
    }
    #[doc = "Bit 10 - The enable bit for the interrupt triggered when event_f1 starts."]
    #[inline(always)]
    pub fn fault1(&mut self) -> FAULT1_W<'_, INT_ENA_SPEC> {
        FAULT1_W::new(self, 10)
    }
    #[doc = "Bit 11 - The enable bit for the interrupt triggered when event_f2 starts."]
    #[inline(always)]
    pub fn fault2(&mut self) -> FAULT2_W<'_, INT_ENA_SPEC> {
        FAULT2_W::new(self, 11)
    }
    #[doc = "Bit 12 - The enable bit for the interrupt triggered when event_f0 ends."]
    #[inline(always)]
    pub fn fault0_clr(&mut self) -> FAULT0_CLR_W<'_, INT_ENA_SPEC> {
        FAULT0_CLR_W::new(self, 12)
    }
    #[doc = "Bit 13 - The enable bit for the interrupt triggered when event_f1 ends."]
    #[inline(always)]
    pub fn fault1_clr(&mut self) -> FAULT1_CLR_W<'_, INT_ENA_SPEC> {
        FAULT1_CLR_W::new(self, 13)
    }
    #[doc = "Bit 14 - The enable bit for the interrupt triggered when event_f2 ends."]
    #[inline(always)]
    pub fn fault2_clr(&mut self) -> FAULT2_CLR_W<'_, INT_ENA_SPEC> {
        FAULT2_CLR_W::new(self, 14)
    }
    #[doc = "Bit 15 - The enable bit for the interrupt triggered by a PWM operator 0 TEA event"]
    #[inline(always)]
    pub fn cmpr0_tea(&mut self) -> CMPR0_TEA_W<'_, INT_ENA_SPEC> {
        CMPR0_TEA_W::new(self, 15)
    }
    #[doc = "Bit 16 - The enable bit for the interrupt triggered by a PWM operator 1 TEA event"]
    #[inline(always)]
    pub fn cmpr1_tea(&mut self) -> CMPR1_TEA_W<'_, INT_ENA_SPEC> {
        CMPR1_TEA_W::new(self, 16)
    }
    #[doc = "Bit 17 - The enable bit for the interrupt triggered by a PWM operator 2 TEA event"]
    #[inline(always)]
    pub fn cmpr2_tea(&mut self) -> CMPR2_TEA_W<'_, INT_ENA_SPEC> {
        CMPR2_TEA_W::new(self, 17)
    }
    #[doc = "Bit 18 - The enable bit for the interrupt triggered by a PWM operator 0 TEB event"]
    #[inline(always)]
    pub fn cmpr0_teb(&mut self) -> CMPR0_TEB_W<'_, INT_ENA_SPEC> {
        CMPR0_TEB_W::new(self, 18)
    }
    #[doc = "Bit 19 - The enable bit for the interrupt triggered by a PWM operator 1 TEB event"]
    #[inline(always)]
    pub fn cmpr1_teb(&mut self) -> CMPR1_TEB_W<'_, INT_ENA_SPEC> {
        CMPR1_TEB_W::new(self, 19)
    }
    #[doc = "Bit 20 - The enable bit for the interrupt triggered by a PWM operator 2 TEB event"]
    #[inline(always)]
    pub fn cmpr2_teb(&mut self) -> CMPR2_TEB_W<'_, INT_ENA_SPEC> {
        CMPR2_TEB_W::new(self, 20)
    }
    #[doc = "Bit 21 - The enable bit for the interrupt triggered by a cycle-by-cycle mode action on PWM0."]
    #[inline(always)]
    pub fn tz0_cbc(&mut self) -> TZ0_CBC_W<'_, INT_ENA_SPEC> {
        TZ0_CBC_W::new(self, 21)
    }
    #[doc = "Bit 22 - The enable bit for the interrupt triggered by a cycle-by-cycle mode action on PWM1."]
    #[inline(always)]
    pub fn tz1_cbc(&mut self) -> TZ1_CBC_W<'_, INT_ENA_SPEC> {
        TZ1_CBC_W::new(self, 22)
    }
    #[doc = "Bit 23 - The enable bit for the interrupt triggered by a cycle-by-cycle mode action on PWM2."]
    #[inline(always)]
    pub fn tz2_cbc(&mut self) -> TZ2_CBC_W<'_, INT_ENA_SPEC> {
        TZ2_CBC_W::new(self, 23)
    }
    #[doc = "Bit 24 - The enable bit for the interrupt triggered by a one-shot mode action on PWM0."]
    #[inline(always)]
    pub fn tz0_ost(&mut self) -> TZ0_OST_W<'_, INT_ENA_SPEC> {
        TZ0_OST_W::new(self, 24)
    }
    #[doc = "Bit 25 - The enable bit for the interrupt triggered by a one-shot mode action on PWM1."]
    #[inline(always)]
    pub fn tz1_ost(&mut self) -> TZ1_OST_W<'_, INT_ENA_SPEC> {
        TZ1_OST_W::new(self, 25)
    }
    #[doc = "Bit 26 - The enable bit for the interrupt triggered by a one-shot mode action on PWM2."]
    #[inline(always)]
    pub fn tz2_ost(&mut self) -> TZ2_OST_W<'_, INT_ENA_SPEC> {
        TZ2_OST_W::new(self, 26)
    }
    #[doc = "Bit 27 - The enable bit for the interrupt triggered by capture on channel 0."]
    #[inline(always)]
    pub fn cap0(&mut self) -> CAP0_W<'_, INT_ENA_SPEC> {
        CAP0_W::new(self, 27)
    }
    #[doc = "Bit 28 - The enable bit for the interrupt triggered by capture on channel 1."]
    #[inline(always)]
    pub fn cap1(&mut self) -> CAP1_W<'_, INT_ENA_SPEC> {
        CAP1_W::new(self, 28)
    }
    #[doc = "Bit 29 - The enable bit for the interrupt triggered by capture on channel 2."]
    #[inline(always)]
    pub fn cap2(&mut self) -> CAP2_W<'_, INT_ENA_SPEC> {
        CAP2_W::new(self, 29)
    }
}
#[doc = "Interrupt enable bits\n\nYou can [`read`](crate::Reg::read) this register and get [`int_ena::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`int_ena::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INT_ENA_SPEC;
impl crate::RegisterSpec for INT_ENA_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`int_ena::R`](R) reader structure"]
impl crate::Readable for INT_ENA_SPEC {}
#[doc = "`write(|w| ..)` method takes [`int_ena::W`](W) writer structure"]
impl crate::Writable for INT_ENA_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets INT_ENA to value 0"]
impl crate::Resettable for INT_ENA_SPEC {}
