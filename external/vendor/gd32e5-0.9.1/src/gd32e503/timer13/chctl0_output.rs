#[doc = "Register `CHCTL0_Output` reader"]
pub type R = crate::R<Chctl0OutputSpec>;
#[doc = "Register `CHCTL0_Output` writer"]
pub type W = crate::W<Chctl0OutputSpec>;
#[doc = "Channel 0 compare output control"]
pub use crate::gd32e503::timer0::chctl0_output::Ch0comctl;
#[doc = "Field `CH0COMCTL` reader - Channel 0 compare output control"]
pub use crate::gd32e503::timer0::chctl0_output::Ch0comctlR;
#[doc = "Field `CH0COMCTL` writer - Channel 0 compare output control"]
pub use crate::gd32e503::timer0::chctl0_output::Ch0comctlW;
#[doc = "Channel 0 output compare fast enable"]
pub use crate::gd32e503::timer0::chctl0_output::Ch0comfen;
#[doc = "Field `CH0COMFEN` reader - Channel 0 output compare fast enable"]
pub use crate::gd32e503::timer0::chctl0_output::Ch0comfenR;
#[doc = "Field `CH0COMFEN` writer - Channel 0 output compare fast enable"]
pub use crate::gd32e503::timer0::chctl0_output::Ch0comfenW;
#[doc = "Channel 0 compare output shadow enable"]
pub use crate::gd32e503::timer0::chctl0_output::Ch0comsen;
#[doc = "Field `CH0COMSEN` reader - Channel 0 compare output shadow enable"]
pub use crate::gd32e503::timer0::chctl0_output::Ch0comsenR;
#[doc = "Field `CH0COMSEN` writer - Channel 0 compare output shadow enable"]
pub use crate::gd32e503::timer0::chctl0_output::Ch0comsenW;
#[doc = "Channel 0 I/O mode selection"]
pub use crate::gd32e503::timer0::chctl0_output::Ch0ms;
#[doc = "Field `CH0MS` reader - Channel 0 I/O mode selection"]
pub use crate::gd32e503::timer0::chctl0_output::Ch0msR;
#[doc = "Field `CH0MS` writer - Channel 0 I/O mode selection"]
pub use crate::gd32e503::timer0::chctl0_output::Ch0msW;
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
