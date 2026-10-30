#[doc = "Register `CTL0` reader"]
pub type R = crate::R<Ctl0Spec>;
#[doc = "Register `CTL0` writer"]
pub type W = crate::W<Ctl0Spec>;
#[doc = "Field `SLP_HOLD` reader - Sleep mode hold register"]
pub type SlpHoldR = crate::BitReader;
#[doc = "Field `SLP_HOLD` writer - Sleep mode hold register"]
pub type SlpHoldW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DSLP_HOLD` reader - Deep-sleep mode hold register"]
pub type DslpHoldR = crate::BitReader;
#[doc = "Field `DSLP_HOLD` writer - Deep-sleep mode hold register"]
pub type DslpHoldW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `STB_HOLD` reader - Standby mode hold register"]
pub type StbHoldR = crate::BitReader;
#[doc = "Field `STB_HOLD` writer - Standby mode hold register"]
pub type StbHoldW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TRACE_IOEN` reader - Trace pin allocation enable"]
pub type TraceIoenR = crate::BitReader;
#[doc = "Field `TRACE_IOEN` writer - Trace pin allocation enable"]
pub type TraceIoenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TRACE_MODE` reader - Trace pin allocation mode"]
pub type TraceModeR = crate::FieldReader;
#[doc = "Field `TRACE_MODE` writer - Trace pin allocation mode"]
pub type TraceModeW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `FWDGT_HOLD` reader - FWDGT hold bit"]
pub type FwdgtHoldR = crate::BitReader;
#[doc = "Field `FWDGT_HOLD` writer - FWDGT hold bit"]
pub type FwdgtHoldW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WWDGT_HOLD` reader - WWDGT hold bit"]
pub type WwdgtHoldR = crate::BitReader;
#[doc = "Field `WWDGT_HOLD` writer - WWDGT hold bit"]
pub type WwdgtHoldW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER0_HOLD` reader - TIMER 0 hold bit"]
pub type Timer0HoldR = crate::BitReader;
#[doc = "Field `TIMER0_HOLD` writer - TIMER 0 hold bit"]
pub type Timer0HoldW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER1_HOLD` reader - TIMER 1 hold bit"]
pub type Timer1HoldR = crate::BitReader;
#[doc = "Field `TIMER1_HOLD` writer - TIMER 1 hold bit"]
pub type Timer1HoldW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER2_HOLD` reader - TIMER 2 hold bit"]
pub type Timer2HoldR = crate::BitReader;
#[doc = "Field `TIMER2_HOLD` writer - TIMER 2 hold bit"]
pub type Timer2HoldW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER3_HOLD` reader - TIMER 23 hold bit"]
pub type Timer3HoldR = crate::BitReader;
#[doc = "Field `TIMER3_HOLD` writer - TIMER 23 hold bit"]
pub type Timer3HoldW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CAN0_HOLD` reader - CAN0 hold bit"]
pub type Can0HoldR = crate::BitReader;
#[doc = "Field `CAN0_HOLD` writer - CAN0 hold bit"]
pub type Can0HoldW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `I2C0_HOLD` reader - I2C0 hold bit"]
pub type I2c0HoldR = crate::BitReader;
#[doc = "Field `I2C0_HOLD` writer - I2C0 hold bit"]
pub type I2c0HoldW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `I2C1_HOLD` reader - I2C1 hold bit"]
pub type I2c1HoldR = crate::BitReader;
#[doc = "Field `I2C1_HOLD` writer - I2C1 hold bit"]
pub type I2c1HoldW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER7_HOLD` reader - TIMER7_HOLD"]
pub type Timer7HoldR = crate::BitReader;
#[doc = "Field `TIMER7_HOLD` writer - TIMER7_HOLD"]
pub type Timer7HoldW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER4_HOLD` reader - TIMER4_HOLD"]
pub type Timer4HoldR = crate::BitReader;
#[doc = "Field `TIMER4_HOLD` writer - TIMER4_HOLD"]
pub type Timer4HoldW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER5_HOLD` reader - TIMER 5 hold bit"]
pub type Timer5HoldR = crate::BitReader;
#[doc = "Field `TIMER5_HOLD` writer - TIMER 5 hold bit"]
pub type Timer5HoldW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER6_HOLD` reader - TIMER 6 hold bit"]
pub type Timer6HoldR = crate::BitReader;
#[doc = "Field `TIMER6_HOLD` writer - TIMER 6 hold bit"]
pub type Timer6HoldW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CAN1_HOLD` reader - CAN1 hold bit"]
pub type Can1HoldR = crate::BitReader;
#[doc = "Field `CAN1_HOLD` writer - CAN1 hold bit"]
pub type Can1HoldW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `I2C2_HOLD` reader - I2C2 hold bit"]
pub type I2c2HoldR = crate::BitReader;
#[doc = "Field `I2C2_HOLD` writer - I2C2 hold bit"]
pub type I2c2HoldW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER11_HOLD` reader - TIMER 11 hold bit"]
pub type Timer11HoldR = crate::BitReader;
#[doc = "Field `TIMER11_HOLD` writer - TIMER 11 hold bit"]
pub type Timer11HoldW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER12_HOLD` reader - TIMER 12 hold bit"]
pub type Timer12HoldR = crate::BitReader;
#[doc = "Field `TIMER12_HOLD` writer - TIMER 12 hold bit"]
pub type Timer12HoldW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER13_HOLD` reader - TIMER 13 hold bit"]
pub type Timer13HoldR = crate::BitReader;
#[doc = "Field `TIMER13_HOLD` writer - TIMER 13 hold bit"]
pub type Timer13HoldW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER8_HOLD` reader - TIMER 8 hold bit"]
pub type Timer8HoldR = crate::BitReader;
#[doc = "Field `TIMER8_HOLD` writer - TIMER 8 hold bit"]
pub type Timer8HoldW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER9_HOLD` reader - TIMER 9 hold bit"]
pub type Timer9HoldR = crate::BitReader;
#[doc = "Field `TIMER9_HOLD` writer - TIMER 9 hold bit"]
pub type Timer9HoldW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMER10_HOLD` reader - TIMER 10 hold bit"]
pub type Timer10HoldR = crate::BitReader;
#[doc = "Field `TIMER10_HOLD` writer - TIMER 10 hold bit"]
pub type Timer10HoldW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SHRTIMER_HOLD` reader - SHRTIMER hold bit"]
pub type ShrtimerHoldR = crate::BitReader;
#[doc = "Field `SHRTIMER_HOLD` writer - SHRTIMER hold bit"]
pub type ShrtimerHoldW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Sleep mode hold register"]
    #[inline(always)]
    pub fn slp_hold(&self) -> SlpHoldR {
        SlpHoldR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Deep-sleep mode hold register"]
    #[inline(always)]
    pub fn dslp_hold(&self) -> DslpHoldR {
        DslpHoldR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Standby mode hold register"]
    #[inline(always)]
    pub fn stb_hold(&self) -> StbHoldR {
        StbHoldR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 5 - Trace pin allocation enable"]
    #[inline(always)]
    pub fn trace_ioen(&self) -> TraceIoenR {
        TraceIoenR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bits 6:7 - Trace pin allocation mode"]
    #[inline(always)]
    pub fn trace_mode(&self) -> TraceModeR {
        TraceModeR::new(((self.bits >> 6) & 3) as u8)
    }
    #[doc = "Bit 8 - FWDGT hold bit"]
    #[inline(always)]
    pub fn fwdgt_hold(&self) -> FwdgtHoldR {
        FwdgtHoldR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - WWDGT hold bit"]
    #[inline(always)]
    pub fn wwdgt_hold(&self) -> WwdgtHoldR {
        WwdgtHoldR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - TIMER 0 hold bit"]
    #[inline(always)]
    pub fn timer0_hold(&self) -> Timer0HoldR {
        Timer0HoldR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - TIMER 1 hold bit"]
    #[inline(always)]
    pub fn timer1_hold(&self) -> Timer1HoldR {
        Timer1HoldR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - TIMER 2 hold bit"]
    #[inline(always)]
    pub fn timer2_hold(&self) -> Timer2HoldR {
        Timer2HoldR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - TIMER 23 hold bit"]
    #[inline(always)]
    pub fn timer3_hold(&self) -> Timer3HoldR {
        Timer3HoldR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - CAN0 hold bit"]
    #[inline(always)]
    pub fn can0_hold(&self) -> Can0HoldR {
        Can0HoldR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - I2C0 hold bit"]
    #[inline(always)]
    pub fn i2c0_hold(&self) -> I2c0HoldR {
        I2c0HoldR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - I2C1 hold bit"]
    #[inline(always)]
    pub fn i2c1_hold(&self) -> I2c1HoldR {
        I2c1HoldR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - TIMER7_HOLD"]
    #[inline(always)]
    pub fn timer7_hold(&self) -> Timer7HoldR {
        Timer7HoldR::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - TIMER4_HOLD"]
    #[inline(always)]
    pub fn timer4_hold(&self) -> Timer4HoldR {
        Timer4HoldR::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - TIMER 5 hold bit"]
    #[inline(always)]
    pub fn timer5_hold(&self) -> Timer5HoldR {
        Timer5HoldR::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - TIMER 6 hold bit"]
    #[inline(always)]
    pub fn timer6_hold(&self) -> Timer6HoldR {
        Timer6HoldR::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - CAN1 hold bit"]
    #[inline(always)]
    pub fn can1_hold(&self) -> Can1HoldR {
        Can1HoldR::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 22 - I2C2 hold bit"]
    #[inline(always)]
    pub fn i2c2_hold(&self) -> I2c2HoldR {
        I2c2HoldR::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 25 - TIMER 11 hold bit"]
    #[inline(always)]
    pub fn timer11_hold(&self) -> Timer11HoldR {
        Timer11HoldR::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - TIMER 12 hold bit"]
    #[inline(always)]
    pub fn timer12_hold(&self) -> Timer12HoldR {
        Timer12HoldR::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - TIMER 13 hold bit"]
    #[inline(always)]
    pub fn timer13_hold(&self) -> Timer13HoldR {
        Timer13HoldR::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - TIMER 8 hold bit"]
    #[inline(always)]
    pub fn timer8_hold(&self) -> Timer8HoldR {
        Timer8HoldR::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - TIMER 9 hold bit"]
    #[inline(always)]
    pub fn timer9_hold(&self) -> Timer9HoldR {
        Timer9HoldR::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - TIMER 10 hold bit"]
    #[inline(always)]
    pub fn timer10_hold(&self) -> Timer10HoldR {
        Timer10HoldR::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - SHRTIMER hold bit"]
    #[inline(always)]
    pub fn shrtimer_hold(&self) -> ShrtimerHoldR {
        ShrtimerHoldR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Sleep mode hold register"]
    #[inline(always)]
    #[must_use]
    pub fn slp_hold(&mut self) -> SlpHoldW<Ctl0Spec> {
        SlpHoldW::new(self, 0)
    }
    #[doc = "Bit 1 - Deep-sleep mode hold register"]
    #[inline(always)]
    #[must_use]
    pub fn dslp_hold(&mut self) -> DslpHoldW<Ctl0Spec> {
        DslpHoldW::new(self, 1)
    }
    #[doc = "Bit 2 - Standby mode hold register"]
    #[inline(always)]
    #[must_use]
    pub fn stb_hold(&mut self) -> StbHoldW<Ctl0Spec> {
        StbHoldW::new(self, 2)
    }
    #[doc = "Bit 5 - Trace pin allocation enable"]
    #[inline(always)]
    #[must_use]
    pub fn trace_ioen(&mut self) -> TraceIoenW<Ctl0Spec> {
        TraceIoenW::new(self, 5)
    }
    #[doc = "Bits 6:7 - Trace pin allocation mode"]
    #[inline(always)]
    #[must_use]
    pub fn trace_mode(&mut self) -> TraceModeW<Ctl0Spec> {
        TraceModeW::new(self, 6)
    }
    #[doc = "Bit 8 - FWDGT hold bit"]
    #[inline(always)]
    #[must_use]
    pub fn fwdgt_hold(&mut self) -> FwdgtHoldW<Ctl0Spec> {
        FwdgtHoldW::new(self, 8)
    }
    #[doc = "Bit 9 - WWDGT hold bit"]
    #[inline(always)]
    #[must_use]
    pub fn wwdgt_hold(&mut self) -> WwdgtHoldW<Ctl0Spec> {
        WwdgtHoldW::new(self, 9)
    }
    #[doc = "Bit 10 - TIMER 0 hold bit"]
    #[inline(always)]
    #[must_use]
    pub fn timer0_hold(&mut self) -> Timer0HoldW<Ctl0Spec> {
        Timer0HoldW::new(self, 10)
    }
    #[doc = "Bit 11 - TIMER 1 hold bit"]
    #[inline(always)]
    #[must_use]
    pub fn timer1_hold(&mut self) -> Timer1HoldW<Ctl0Spec> {
        Timer1HoldW::new(self, 11)
    }
    #[doc = "Bit 12 - TIMER 2 hold bit"]
    #[inline(always)]
    #[must_use]
    pub fn timer2_hold(&mut self) -> Timer2HoldW<Ctl0Spec> {
        Timer2HoldW::new(self, 12)
    }
    #[doc = "Bit 13 - TIMER 23 hold bit"]
    #[inline(always)]
    #[must_use]
    pub fn timer3_hold(&mut self) -> Timer3HoldW<Ctl0Spec> {
        Timer3HoldW::new(self, 13)
    }
    #[doc = "Bit 14 - CAN0 hold bit"]
    #[inline(always)]
    #[must_use]
    pub fn can0_hold(&mut self) -> Can0HoldW<Ctl0Spec> {
        Can0HoldW::new(self, 14)
    }
    #[doc = "Bit 15 - I2C0 hold bit"]
    #[inline(always)]
    #[must_use]
    pub fn i2c0_hold(&mut self) -> I2c0HoldW<Ctl0Spec> {
        I2c0HoldW::new(self, 15)
    }
    #[doc = "Bit 16 - I2C1 hold bit"]
    #[inline(always)]
    #[must_use]
    pub fn i2c1_hold(&mut self) -> I2c1HoldW<Ctl0Spec> {
        I2c1HoldW::new(self, 16)
    }
    #[doc = "Bit 17 - TIMER7_HOLD"]
    #[inline(always)]
    #[must_use]
    pub fn timer7_hold(&mut self) -> Timer7HoldW<Ctl0Spec> {
        Timer7HoldW::new(self, 17)
    }
    #[doc = "Bit 18 - TIMER4_HOLD"]
    #[inline(always)]
    #[must_use]
    pub fn timer4_hold(&mut self) -> Timer4HoldW<Ctl0Spec> {
        Timer4HoldW::new(self, 18)
    }
    #[doc = "Bit 19 - TIMER 5 hold bit"]
    #[inline(always)]
    #[must_use]
    pub fn timer5_hold(&mut self) -> Timer5HoldW<Ctl0Spec> {
        Timer5HoldW::new(self, 19)
    }
    #[doc = "Bit 20 - TIMER 6 hold bit"]
    #[inline(always)]
    #[must_use]
    pub fn timer6_hold(&mut self) -> Timer6HoldW<Ctl0Spec> {
        Timer6HoldW::new(self, 20)
    }
    #[doc = "Bit 21 - CAN1 hold bit"]
    #[inline(always)]
    #[must_use]
    pub fn can1_hold(&mut self) -> Can1HoldW<Ctl0Spec> {
        Can1HoldW::new(self, 21)
    }
    #[doc = "Bit 22 - I2C2 hold bit"]
    #[inline(always)]
    #[must_use]
    pub fn i2c2_hold(&mut self) -> I2c2HoldW<Ctl0Spec> {
        I2c2HoldW::new(self, 22)
    }
    #[doc = "Bit 25 - TIMER 11 hold bit"]
    #[inline(always)]
    #[must_use]
    pub fn timer11_hold(&mut self) -> Timer11HoldW<Ctl0Spec> {
        Timer11HoldW::new(self, 25)
    }
    #[doc = "Bit 26 - TIMER 12 hold bit"]
    #[inline(always)]
    #[must_use]
    pub fn timer12_hold(&mut self) -> Timer12HoldW<Ctl0Spec> {
        Timer12HoldW::new(self, 26)
    }
    #[doc = "Bit 27 - TIMER 13 hold bit"]
    #[inline(always)]
    #[must_use]
    pub fn timer13_hold(&mut self) -> Timer13HoldW<Ctl0Spec> {
        Timer13HoldW::new(self, 27)
    }
    #[doc = "Bit 28 - TIMER 8 hold bit"]
    #[inline(always)]
    #[must_use]
    pub fn timer8_hold(&mut self) -> Timer8HoldW<Ctl0Spec> {
        Timer8HoldW::new(self, 28)
    }
    #[doc = "Bit 29 - TIMER 9 hold bit"]
    #[inline(always)]
    #[must_use]
    pub fn timer9_hold(&mut self) -> Timer9HoldW<Ctl0Spec> {
        Timer9HoldW::new(self, 29)
    }
    #[doc = "Bit 30 - TIMER 10 hold bit"]
    #[inline(always)]
    #[must_use]
    pub fn timer10_hold(&mut self) -> Timer10HoldW<Ctl0Spec> {
        Timer10HoldW::new(self, 30)
    }
    #[doc = "Bit 31 - SHRTIMER hold bit"]
    #[inline(always)]
    #[must_use]
    pub fn shrtimer_hold(&mut self) -> ShrtimerHoldW<Ctl0Spec> {
        ShrtimerHoldW::new(self, 31)
    }
}
#[doc = "Control register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl0::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl0::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ctl0Spec;
impl crate::RegisterSpec for Ctl0Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctl0::R`](R) reader structure"]
impl crate::Readable for Ctl0Spec {}
#[doc = "`write(|w| ..)` method takes [`ctl0::W`](W) writer structure"]
impl crate::Writable for Ctl0Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CTL0 to value 0"]
impl crate::Resettable for Ctl0Spec {
    const RESET_VALUE: u32 = 0;
}
