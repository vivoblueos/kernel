#[doc = "Register `CHCTL0_Output` reader"]
pub type R = crate::R<Chctl0OutputSpec>;
#[doc = "Register `CHCTL0_Output` writer"]
pub type W = crate::W<Chctl0OutputSpec>;
#[doc = "Channel 0 output compare clear enable"]
pub use crate::gd32e505::timer0::chctl0_output::Ch0comcen;
#[doc = "Field `CH0COMCEN` reader - Channel 0 output compare clear enable"]
pub use crate::gd32e505::timer0::chctl0_output::Ch0comcenR;
#[doc = "Field `CH1COMCEN` reader - Channel 1 output compare clear enable"]
pub use crate::gd32e505::timer0::chctl0_output::Ch0comcenR as Ch1comcenR;
#[doc = "Field `CH0COMCEN` writer - Channel 0 output compare clear enable"]
pub use crate::gd32e505::timer0::chctl0_output::Ch0comcenW;
#[doc = "Field `CH1COMCEN` writer - Channel 1 output compare clear enable"]
pub use crate::gd32e505::timer0::chctl0_output::Ch0comcenW as Ch1comcenW;
#[doc = "Channel 0 compare output control"]
pub use crate::gd32e505::timer0::chctl0_output::Ch0comctl;
#[doc = "Field `CH0COMCTL` reader - Channel 0 compare output control"]
pub use crate::gd32e505::timer0::chctl0_output::Ch0comctlR;
#[doc = "Field `CH1COMCTL` reader - Channel 1 compare output control"]
pub use crate::gd32e505::timer0::chctl0_output::Ch0comctlR as Ch1comctlR;
#[doc = "Field `CH0COMCTL` writer - Channel 0 compare output control"]
pub use crate::gd32e505::timer0::chctl0_output::Ch0comctlW;
#[doc = "Field `CH1COMCTL` writer - Channel 1 compare output control"]
pub use crate::gd32e505::timer0::chctl0_output::Ch0comctlW as Ch1comctlW;
#[doc = "Channel 0 output compare fast enable"]
pub use crate::gd32e505::timer0::chctl0_output::Ch0comfen;
#[doc = "Field `CH0COMFEN` reader - Channel 0 output compare fast enable"]
pub use crate::gd32e505::timer0::chctl0_output::Ch0comfenR;
#[doc = "Field `CH1COMFEN` reader - Channel 1 output compare fast enable"]
pub use crate::gd32e505::timer0::chctl0_output::Ch0comfenR as Ch1comfenR;
#[doc = "Field `CH0COMFEN` writer - Channel 0 output compare fast enable"]
pub use crate::gd32e505::timer0::chctl0_output::Ch0comfenW;
#[doc = "Field `CH1COMFEN` writer - Channel 1 output compare fast enable"]
pub use crate::gd32e505::timer0::chctl0_output::Ch0comfenW as Ch1comfenW;
#[doc = "Channel 0 compare output shadow enable"]
pub use crate::gd32e505::timer0::chctl0_output::Ch0comsen;
#[doc = "Field `CH0COMSEN` reader - Channel 0 compare output shadow enable"]
pub use crate::gd32e505::timer0::chctl0_output::Ch0comsenR;
#[doc = "Field `CH1COMSEN` reader - Channel 1 output compare shadow enable"]
pub use crate::gd32e505::timer0::chctl0_output::Ch0comsenR as Ch1comsenR;
#[doc = "Field `CH0COMSEN` writer - Channel 0 compare output shadow enable"]
pub use crate::gd32e505::timer0::chctl0_output::Ch0comsenW;
#[doc = "Field `CH1COMSEN` writer - Channel 1 output compare shadow enable"]
pub use crate::gd32e505::timer0::chctl0_output::Ch0comsenW as Ch1comsenW;
#[doc = "Channel 0 I/O mode selection"]
pub use crate::gd32e505::timer0::chctl0_output::Ch0ms;
#[doc = "Field `CH0MS` reader - Channel 0 I/O mode selection"]
pub use crate::gd32e505::timer0::chctl0_output::Ch0msR;
#[doc = "Field `CH1MS` reader - Channel 1 mode selection"]
pub use crate::gd32e505::timer0::chctl0_output::Ch0msR as Ch1msR;
#[doc = "Field `CH0MS` writer - Channel 0 I/O mode selection"]
pub use crate::gd32e505::timer0::chctl0_output::Ch0msW;
#[doc = "Field `CH1MS` writer - Channel 1 mode selection"]
pub use crate::gd32e505::timer0::chctl0_output::Ch0msW as Ch1msW;
impl R {
    #[doc = "Bits 0:1 - Channel 0 I/O mode selection"]
    #[inline(always)]
    pub fn ch0ms(&self) -> Ch0msR {
        Ch0msR::new((self.bits & 3) as u8)
    }
    #[doc = "Bit 2 - Channel 0 output compare fast enable"]
    #[inline(always)]
    pub fn ch0comfen(&self) -> Ch0comfenR {
        Ch0comfenR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Channel 0 compare output shadow enable"]
    #[inline(always)]
    pub fn ch0comsen(&self) -> Ch0comsenR {
        Ch0comsenR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bits 4:6 - Channel 0 compare output control"]
    #[inline(always)]
    pub fn ch0comctl(&self) -> Ch0comctlR {
        Ch0comctlR::new(((self.bits >> 4) & 7) as u8)
    }
    #[doc = "Bit 7 - Channel 0 output compare clear enable"]
    #[inline(always)]
    pub fn ch0comcen(&self) -> Ch0comcenR {
        Ch0comcenR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bits 8:9 - Channel 1 mode selection"]
    #[inline(always)]
    pub fn ch1ms(&self) -> Ch1msR {
        Ch1msR::new(((self.bits >> 8) & 3) as u8)
    }
    #[doc = "Bit 10 - Channel 1 output compare fast enable"]
    #[inline(always)]
    pub fn ch1comfen(&self) -> Ch1comfenR {
        Ch1comfenR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Channel 1 output compare shadow enable"]
    #[inline(always)]
    pub fn ch1comsen(&self) -> Ch1comsenR {
        Ch1comsenR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bits 12:14 - Channel 1 compare output control"]
    #[inline(always)]
    pub fn ch1comctl(&self) -> Ch1comctlR {
        Ch1comctlR::new(((self.bits >> 12) & 7) as u8)
    }
    #[doc = "Bit 15 - Channel 1 output compare clear enable"]
    #[inline(always)]
    pub fn ch1comcen(&self) -> Ch1comcenR {
        Ch1comcenR::new(((self.bits >> 15) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:1 - Channel 0 I/O mode selection"]
    #[inline(always)]
    #[must_use]
    pub fn ch0ms(&mut self) -> Ch0msW<Chctl0OutputSpec> {
        Ch0msW::new(self, 0)
    }
    #[doc = "Bit 2 - Channel 0 output compare fast enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch0comfen(&mut self) -> Ch0comfenW<Chctl0OutputSpec> {
        Ch0comfenW::new(self, 2)
    }
    #[doc = "Bit 3 - Channel 0 compare output shadow enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch0comsen(&mut self) -> Ch0comsenW<Chctl0OutputSpec> {
        Ch0comsenW::new(self, 3)
    }
    #[doc = "Bits 4:6 - Channel 0 compare output control"]
    #[inline(always)]
    #[must_use]
    pub fn ch0comctl(&mut self) -> Ch0comctlW<Chctl0OutputSpec> {
        Ch0comctlW::new(self, 4)
    }
    #[doc = "Bit 7 - Channel 0 output compare clear enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch0comcen(&mut self) -> Ch0comcenW<Chctl0OutputSpec> {
        Ch0comcenW::new(self, 7)
    }
    #[doc = "Bits 8:9 - Channel 1 mode selection"]
    #[inline(always)]
    #[must_use]
    pub fn ch1ms(&mut self) -> Ch1msW<Chctl0OutputSpec> {
        Ch1msW::new(self, 8)
    }
    #[doc = "Bit 10 - Channel 1 output compare fast enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch1comfen(&mut self) -> Ch1comfenW<Chctl0OutputSpec> {
        Ch1comfenW::new(self, 10)
    }
    #[doc = "Bit 11 - Channel 1 output compare shadow enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch1comsen(&mut self) -> Ch1comsenW<Chctl0OutputSpec> {
        Ch1comsenW::new(self, 11)
    }
    #[doc = "Bits 12:14 - Channel 1 compare output control"]
    #[inline(always)]
    #[must_use]
    pub fn ch1comctl(&mut self) -> Ch1comctlW<Chctl0OutputSpec> {
        Ch1comctlW::new(self, 12)
    }
    #[doc = "Bit 15 - Channel 1 output compare clear enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch1comcen(&mut self) -> Ch1comcenW<Chctl0OutputSpec> {
        Ch1comcenW::new(self, 15)
    }
}
#[doc = "Channel control register 0 (output mode)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`chctl0_output::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`chctl0_output::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Chctl0OutputSpec;
impl crate::RegisterSpec for Chctl0OutputSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`chctl0_output::R`](R) reader structure"]
impl crate::Readable for Chctl0OutputSpec {}
#[doc = "`write(|w| ..)` method takes [`chctl0_output::W`](W) writer structure"]
impl crate::Writable for Chctl0OutputSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CHCTL0_Output to value 0"]
impl crate::Resettable for Chctl0OutputSpec {
    const RESET_VALUE: u32 = 0;
}
