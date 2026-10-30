#[doc = "Register `CFG0` reader"]
pub type R = crate::R<CFG0_SPEC>;
#[doc = "Register `CFG0` writer"]
pub type W = crate::W<CFG0_SPEC>;
#[doc = "Field `PRESCALE` reader - period of PT0_clk = Period of PWM_clk * (PWM_TIMER0_PRESCALE + 1)"]
pub type PRESCALE_R = crate::FieldReader;
#[doc = "Field `PRESCALE` writer - period of PT0_clk = Period of PWM_clk * (PWM_TIMER0_PRESCALE + 1)"]
pub type PRESCALE_W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `PERIOD` reader - period shadow register of PWM timer0"]
pub type PERIOD_R = crate::FieldReader<u16>;
#[doc = "Field `PERIOD` writer - period shadow register of PWM timer0"]
pub type PERIOD_W<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
#[doc = "Field `PERIOD_UPMETHOD` reader - Update method for active register of PWM timer0 period, 0: immediate, 1: TEZ, 2: sync, 3: TEZ | sync. TEZ here and below means timer equal zero event"]
pub type PERIOD_UPMETHOD_R = crate::FieldReader;
#[doc = "Field `PERIOD_UPMETHOD` writer - Update method for active register of PWM timer0 period, 0: immediate, 1: TEZ, 2: sync, 3: TEZ | sync. TEZ here and below means timer equal zero event"]
pub type PERIOD_UPMETHOD_W<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:7 - period of PT0_clk = Period of PWM_clk * (PWM_TIMER0_PRESCALE + 1)"]
    #[inline(always)]
    pub fn prescale(&self) -> PRESCALE_R {
        PRESCALE_R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:23 - period shadow register of PWM timer0"]
    #[inline(always)]
    pub fn period(&self) -> PERIOD_R {
        PERIOD_R::new(((self.bits >> 8) & 0xffff) as u16)
    }
    #[doc = "Bits 24:25 - Update method for active register of PWM timer0 period, 0: immediate, 1: TEZ, 2: sync, 3: TEZ | sync. TEZ here and below means timer equal zero event"]
    #[inline(always)]
    pub fn period_upmethod(&self) -> PERIOD_UPMETHOD_R {
        PERIOD_UPMETHOD_R::new(((self.bits >> 24) & 3) as u8)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("CFG0")
            .field("prescale", &self.prescale())
            .field("period", &self.period())
            .field("period_upmethod", &self.period_upmethod())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:7 - period of PT0_clk = Period of PWM_clk * (PWM_TIMER0_PRESCALE + 1)"]
    #[inline(always)]
    pub fn prescale(&mut self) -> PRESCALE_W<'_, CFG0_SPEC> {
        PRESCALE_W::new(self, 0)
    }
    #[doc = "Bits 8:23 - period shadow register of PWM timer0"]
    #[inline(always)]
    pub fn period(&mut self) -> PERIOD_W<'_, CFG0_SPEC> {
        PERIOD_W::new(self, 8)
    }
    #[doc = "Bits 24:25 - Update method for active register of PWM timer0 period, 0: immediate, 1: TEZ, 2: sync, 3: TEZ | sync. TEZ here and below means timer equal zero event"]
    #[inline(always)]
    pub fn period_upmethod(&mut self) -> PERIOD_UPMETHOD_W<'_, CFG0_SPEC> {
        PERIOD_UPMETHOD_W::new(self, 24)
    }
}
#[doc = "PWM TIMERx period and update method configuration register.\n\nYou can [`read`](crate::Reg::read) this register and get [`cfg0::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`cfg0::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CFG0_SPEC;
impl crate::RegisterSpec for CFG0_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`cfg0::R`](R) reader structure"]
impl crate::Readable for CFG0_SPEC {}
#[doc = "`write(|w| ..)` method takes [`cfg0::W`](W) writer structure"]
impl crate::Writable for CFG0_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets CFG0 to value 0xff00"]
impl crate::Resettable for CFG0_SPEC {
    const RESET_VALUE: u32 = 0xff00;
}
