#[doc = "Register `CHCTL2` reader"]
pub type R = crate::R<Chctl2Spec>;
#[doc = "Register `CHCTL2` writer"]
pub type W = crate::W<Chctl2Spec>;
#[doc = "Channel 0 capture/compare function enable"]
pub use crate::gd32e508::timer0::chctl2::Ch0en;
#[doc = "Field `CH0EN` reader - Channel 0 capture/compare function enable"]
pub use crate::gd32e508::timer0::chctl2::Ch0enR;
#[doc = "Field `CH0EN` writer - Channel 0 capture/compare function enable"]
pub use crate::gd32e508::timer0::chctl2::Ch0enW;
#[doc = "Channel 0 capture/compare polarity"]
pub use crate::gd32e508::timer0::chctl2::Ch0p;
#[doc = "Field `CH0P` reader - Channel 0 capture/compare polarity"]
pub use crate::gd32e508::timer0::chctl2::Ch0pR;
#[doc = "Field `CH0NP` reader - Channel 0 complementary output polarity"]
pub use crate::gd32e508::timer0::chctl2::Ch0pR as Ch0npR;
#[doc = "Field `CH0P` writer - Channel 0 capture/compare polarity"]
pub use crate::gd32e508::timer0::chctl2::Ch0pW;
#[doc = "Field `CH0NP` writer - Channel 0 complementary output polarity"]
pub use crate::gd32e508::timer0::chctl2::Ch0pW as Ch0npW;
impl R {
    #[doc = "Bit 0 - Channel 0 capture/compare function enable"]
    #[inline(always)]
    pub fn ch0en(&self) -> Ch0enR {
        Ch0enR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Channel 0 capture/compare polarity"]
    #[inline(always)]
    pub fn ch0p(&self) -> Ch0pR {
        Ch0pR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 3 - Channel 0 complementary output polarity"]
    #[inline(always)]
    pub fn ch0np(&self) -> Ch0npR {
        Ch0npR::new(((self.bits >> 3) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Channel 0 capture/compare function enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch0en(&mut self) -> Ch0enW<Chctl2Spec> {
        Ch0enW::new(self, 0)
    }
    #[doc = "Bit 1 - Channel 0 capture/compare polarity"]
    #[inline(always)]
    #[must_use]
    pub fn ch0p(&mut self) -> Ch0pW<Chctl2Spec> {
        Ch0pW::new(self, 1)
    }
    #[doc = "Bit 3 - Channel 0 complementary output polarity"]
    #[inline(always)]
    #[must_use]
    pub fn ch0np(&mut self) -> Ch0npW<Chctl2Spec> {
        Ch0npW::new(self, 3)
    }
}
#[doc = "Channel control register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`chctl2::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`chctl2::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Chctl2Spec;
impl crate::RegisterSpec for Chctl2Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`chctl2::R`](R) reader structure"]
impl crate::Readable for Chctl2Spec {}
#[doc = "`write(|w| ..)` method takes [`chctl2::W`](W) writer structure"]
impl crate::Writable for Chctl2Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CHCTL2 to value 0"]
impl crate::Resettable for Chctl2Spec {
    const RESET_VALUE: u32 = 0;
}
