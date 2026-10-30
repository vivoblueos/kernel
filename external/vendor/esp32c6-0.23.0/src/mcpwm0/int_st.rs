#[doc = "Register `INT_ST` reader"]
pub type R = crate::R<INT_ST_SPEC>;
#[doc = "Field `TIMER0_STOP` reader - The masked status bit for the interrupt triggered when the timer 0 stops."]
pub type TIMER0_STOP_R = crate::BitReader;
#[doc = "Field `TIMER1_STOP` reader - The masked status bit for the interrupt triggered when the timer 1 stops."]
pub type TIMER1_STOP_R = crate::BitReader;
#[doc = "Field `TIMER2_STOP` reader - The masked status bit for the interrupt triggered when the timer 2 stops."]
pub type TIMER2_STOP_R = crate::BitReader;
#[doc = "Field `TIMER0_TEZ` reader - The masked status bit for the interrupt triggered by a PWM timer 0 TEZ event."]
pub type TIMER0_TEZ_R = crate::BitReader;
#[doc = "Field `TIMER1_TEZ` reader - The masked status bit for the interrupt triggered by a PWM timer 1 TEZ event."]
pub type TIMER1_TEZ_R = crate::BitReader;
#[doc = "Field `TIMER2_TEZ` reader - The masked status bit for the interrupt triggered by a PWM timer 2 TEZ event."]
pub type TIMER2_TEZ_R = crate::BitReader;
#[doc = "Field `TIMER0_TEP` reader - The masked status bit for the interrupt triggered by a PWM timer 0 TEP event."]
pub type TIMER0_TEP_R = crate::BitReader;
#[doc = "Field `TIMER1_TEP` reader - The masked status bit for the interrupt triggered by a PWM timer 1 TEP event."]
pub type TIMER1_TEP_R = crate::BitReader;
#[doc = "Field `TIMER2_TEP` reader - The masked status bit for the interrupt triggered by a PWM timer 2 TEP event."]
pub type TIMER2_TEP_R = crate::BitReader;
#[doc = "Field `FAULT0` reader - The masked status bit for the interrupt triggered when event_f0 starts."]
pub type FAULT0_R = crate::BitReader;
#[doc = "Field `FAULT1` reader - The masked status bit for the interrupt triggered when event_f1 starts."]
pub type FAULT1_R = crate::BitReader;
#[doc = "Field `FAULT2` reader - The masked status bit for the interrupt triggered when event_f2 starts."]
pub type FAULT2_R = crate::BitReader;
#[doc = "Field `FAULT0_CLR` reader - The masked status bit for the interrupt triggered when event_f0 ends."]
pub type FAULT0_CLR_R = crate::BitReader;
#[doc = "Field `FAULT1_CLR` reader - The masked status bit for the interrupt triggered when event_f1 ends."]
pub type FAULT1_CLR_R = crate::BitReader;
#[doc = "Field `FAULT2_CLR` reader - The masked status bit for the interrupt triggered when event_f2 ends."]
pub type FAULT2_CLR_R = crate::BitReader;
#[doc = "Field `CMPR0_TEA` reader - The masked status bit for the interrupt triggered by a PWM operator 0 TEA event"]
pub type CMPR0_TEA_R = crate::BitReader;
#[doc = "Field `CMPR1_TEA` reader - The masked status bit for the interrupt triggered by a PWM operator 1 TEA event"]
pub type CMPR1_TEA_R = crate::BitReader;
#[doc = "Field `CMPR2_TEA` reader - The masked status bit for the interrupt triggered by a PWM operator 2 TEA event"]
pub type CMPR2_TEA_R = crate::BitReader;
#[doc = "Field `CMPR0_TEB` reader - The masked status bit for the interrupt triggered by a PWM operator 0 TEB event"]
pub type CMPR0_TEB_R = crate::BitReader;
#[doc = "Field `CMPR1_TEB` reader - The masked status bit for the interrupt triggered by a PWM operator 1 TEB event"]
pub type CMPR1_TEB_R = crate::BitReader;
#[doc = "Field `CMPR2_TEB` reader - The masked status bit for the interrupt triggered by a PWM operator 2 TEB event"]
pub type CMPR2_TEB_R = crate::BitReader;
#[doc = "Field `TZ0_CBC` reader - The masked status bit for the interrupt triggered by a cycle-by-cycle mode action on PWM0."]
pub type TZ0_CBC_R = crate::BitReader;
#[doc = "Field `TZ1_CBC` reader - The masked status bit for the interrupt triggered by a cycle-by-cycle mode action on PWM1."]
pub type TZ1_CBC_R = crate::BitReader;
#[doc = "Field `TZ2_CBC` reader - The masked status bit for the interrupt triggered by a cycle-by-cycle mode action on PWM2."]
pub type TZ2_CBC_R = crate::BitReader;
#[doc = "Field `TZ0_OST` reader - The masked status bit for the interrupt triggered by a one-shot mode action on PWM0."]
pub type TZ0_OST_R = crate::BitReader;
#[doc = "Field `TZ1_OST` reader - The masked status bit for the interrupt triggered by a one-shot mode action on PWM1."]
pub type TZ1_OST_R = crate::BitReader;
#[doc = "Field `TZ2_OST` reader - The masked status bit for the interrupt triggered by a one-shot mode action on PWM2."]
pub type TZ2_OST_R = crate::BitReader;
#[doc = "Field `CAP0` reader - The masked status bit for the interrupt triggered by capture on channel 0."]
pub type CAP0_R = crate::BitReader;
#[doc = "Field `CAP1` reader - The masked status bit for the interrupt triggered by capture on channel 1."]
pub type CAP1_R = crate::BitReader;
#[doc = "Field `CAP2` reader - The masked status bit for the interrupt triggered by capture on channel 2."]
pub type CAP2_R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - The masked status bit for the interrupt triggered when the timer 0 stops."]
    #[inline(always)]
    pub fn timer0_stop(&self) -> TIMER0_STOP_R {
        TIMER0_STOP_R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - The masked status bit for the interrupt triggered when the timer 1 stops."]
    #[inline(always)]
    pub fn timer1_stop(&self) -> TIMER1_STOP_R {
        TIMER1_STOP_R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - The masked status bit for the interrupt triggered when the timer 2 stops."]
    #[inline(always)]
    pub fn timer2_stop(&self) -> TIMER2_STOP_R {
        TIMER2_STOP_R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - The masked status bit for the interrupt triggered by a PWM timer 0 TEZ event."]
    #[inline(always)]
    pub fn timer0_tez(&self) -> TIMER0_TEZ_R {
        TIMER0_TEZ_R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - The masked status bit for the interrupt triggered by a PWM timer 1 TEZ event."]
    #[inline(always)]
    pub fn timer1_tez(&self) -> TIMER1_TEZ_R {
        TIMER1_TEZ_R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - The masked status bit for the interrupt triggered by a PWM timer 2 TEZ event."]
    #[inline(always)]
    pub fn timer2_tez(&self) -> TIMER2_TEZ_R {
        TIMER2_TEZ_R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - The masked status bit for the interrupt triggered by a PWM timer 0 TEP event."]
    #[inline(always)]
    pub fn timer0_tep(&self) -> TIMER0_TEP_R {
        TIMER0_TEP_R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - The masked status bit for the interrupt triggered by a PWM timer 1 TEP event."]
    #[inline(always)]
    pub fn timer1_tep(&self) -> TIMER1_TEP_R {
        TIMER1_TEP_R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - The masked status bit for the interrupt triggered by a PWM timer 2 TEP event."]
    #[inline(always)]
    pub fn timer2_tep(&self) -> TIMER2_TEP_R {
        TIMER2_TEP_R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - The masked status bit for the interrupt triggered when event_f0 starts."]
    #[inline(always)]
    pub fn fault0(&self) -> FAULT0_R {
        FAULT0_R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - The masked status bit for the interrupt triggered when event_f1 starts."]
    #[inline(always)]
    pub fn fault1(&self) -> FAULT1_R {
        FAULT1_R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - The masked status bit for the interrupt triggered when event_f2 starts."]
    #[inline(always)]
    pub fn fault2(&self) -> FAULT2_R {
        FAULT2_R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - The masked status bit for the interrupt triggered when event_f0 ends."]
    #[inline(always)]
    pub fn fault0_clr(&self) -> FAULT0_CLR_R {
        FAULT0_CLR_R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - The masked status bit for the interrupt triggered when event_f1 ends."]
    #[inline(always)]
    pub fn fault1_clr(&self) -> FAULT1_CLR_R {
        FAULT1_CLR_R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - The masked status bit for the interrupt triggered when event_f2 ends."]
    #[inline(always)]
    pub fn fault2_clr(&self) -> FAULT2_CLR_R {
        FAULT2_CLR_R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - The masked status bit for the interrupt triggered by a PWM operator 0 TEA event"]
    #[inline(always)]
    pub fn cmpr0_tea(&self) -> CMPR0_TEA_R {
        CMPR0_TEA_R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - The masked status bit for the interrupt triggered by a PWM operator 1 TEA event"]
    #[inline(always)]
    pub fn cmpr1_tea(&self) -> CMPR1_TEA_R {
        CMPR1_TEA_R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - The masked status bit for the interrupt triggered by a PWM operator 2 TEA event"]
    #[inline(always)]
    pub fn cmpr2_tea(&self) -> CMPR2_TEA_R {
        CMPR2_TEA_R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - The masked status bit for the interrupt triggered by a PWM operator 0 TEB event"]
    #[inline(always)]
    pub fn cmpr0_teb(&self) -> CMPR0_TEB_R {
        CMPR0_TEB_R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - The masked status bit for the interrupt triggered by a PWM operator 1 TEB event"]
    #[inline(always)]
    pub fn cmpr1_teb(&self) -> CMPR1_TEB_R {
        CMPR1_TEB_R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - The masked status bit for the interrupt triggered by a PWM operator 2 TEB event"]
    #[inline(always)]
    pub fn cmpr2_teb(&self) -> CMPR2_TEB_R {
        CMPR2_TEB_R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - The masked status bit for the interrupt triggered by a cycle-by-cycle mode action on PWM0."]
    #[inline(always)]
    pub fn tz0_cbc(&self) -> TZ0_CBC_R {
        TZ0_CBC_R::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 22 - The masked status bit for the interrupt triggered by a cycle-by-cycle mode action on PWM1."]
    #[inline(always)]
    pub fn tz1_cbc(&self) -> TZ1_CBC_R {
        TZ1_CBC_R::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 23 - The masked status bit for the interrupt triggered by a cycle-by-cycle mode action on PWM2."]
    #[inline(always)]
    pub fn tz2_cbc(&self) -> TZ2_CBC_R {
        TZ2_CBC_R::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bit 24 - The masked status bit for the interrupt triggered by a one-shot mode action on PWM0."]
    #[inline(always)]
    pub fn tz0_ost(&self) -> TZ0_OST_R {
        TZ0_OST_R::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - The masked status bit for the interrupt triggered by a one-shot mode action on PWM1."]
    #[inline(always)]
    pub fn tz1_ost(&self) -> TZ1_OST_R {
        TZ1_OST_R::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - The masked status bit for the interrupt triggered by a one-shot mode action on PWM2."]
    #[inline(always)]
    pub fn tz2_ost(&self) -> TZ2_OST_R {
        TZ2_OST_R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - The masked status bit for the interrupt triggered by capture on channel 0."]
    #[inline(always)]
    pub fn cap0(&self) -> CAP0_R {
        CAP0_R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - The masked status bit for the interrupt triggered by capture on channel 1."]
    #[inline(always)]
    pub fn cap1(&self) -> CAP1_R {
        CAP1_R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - The masked status bit for the interrupt triggered by capture on channel 2."]
    #[inline(always)]
    pub fn cap2(&self) -> CAP2_R {
        CAP2_R::new(((self.bits >> 29) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("INT_ST")
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
#[doc = "Masked interrupt status\n\nYou can [`read`](crate::Reg::read) this register and get [`int_st::R`](R). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct INT_ST_SPEC;
impl crate::RegisterSpec for INT_ST_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`int_st::R`](R) reader structure"]
impl crate::Readable for INT_ST_SPEC {}
#[doc = "`reset()` method sets INT_ST to value 0"]
impl crate::Resettable for INT_ST_SPEC {}
