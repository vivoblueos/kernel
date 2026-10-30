#[doc = "Register `INTF` reader"]
pub type R = crate::R<IntfSpec>;
#[doc = "Register `INTF` writer"]
pub type W = crate::W<IntfSpec>;
#[doc = "Channel 0 capture/compare interrupt flag"]
pub use crate::gd32e503::timer0::intf::Ch0if;
#[doc = "Field `CH0IF` reader - Channel 0 capture/compare interrupt flag"]
pub use crate::gd32e503::timer0::intf::Ch0ifR;
#[doc = "Field `CH1IF` reader - Channel 1 capture/compare interrupt flag"]
pub use crate::gd32e503::timer0::intf::Ch0ifR as Ch1ifR;
#[doc = "Field `CH2IF` reader - Channel 2 capture/compare interrupt enable"]
pub use crate::gd32e503::timer0::intf::Ch0ifR as Ch2ifR;
#[doc = "Field `CH3IF` reader - Channel 3 capture/compare interrupt enable"]
pub use crate::gd32e503::timer0::intf::Ch0ifR as Ch3ifR;
#[doc = "Field `CH0IF` writer - Channel 0 capture/compare interrupt flag"]
pub use crate::gd32e503::timer0::intf::Ch0ifW;
#[doc = "Field `CH1IF` writer - Channel 1 capture/compare interrupt flag"]
pub use crate::gd32e503::timer0::intf::Ch0ifW as Ch1ifW;
#[doc = "Field `CH2IF` writer - Channel 2 capture/compare interrupt enable"]
pub use crate::gd32e503::timer0::intf::Ch0ifW as Ch2ifW;
#[doc = "Field `CH3IF` writer - Channel 3 capture/compare interrupt enable"]
pub use crate::gd32e503::timer0::intf::Ch0ifW as Ch3ifW;
#[doc = "Update interrupt flag"]
pub use crate::gd32e503::timer0::intf::Upif;
#[doc = "Field `UPIF` reader - Update interrupt flag"]
pub use crate::gd32e503::timer0::intf::UpifR;
#[doc = "Field `UPIF` writer - Update interrupt flag"]
pub use crate::gd32e503::timer0::intf::UpifW;
#[doc = "Trigger interrupt flag\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Trgif {
    #[doc = "0: No trigger event occured"]
    Clear = 0,
    #[doc = "1: Trigger event occurred"]
    Triggered = 1,
}
impl From<Trgif> for bool {
    #[inline(always)]
    fn from(variant: Trgif) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `TRGIF` reader - Trigger interrupt flag"]
pub type TrgifR = crate::BitReader<Trgif>;
impl TrgifR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Trgif {
        match self.bits {
            false => Trgif::Clear,
            true => Trgif::Triggered,
        }
    }
    #[doc = "No trigger event occured"]
    #[inline(always)]
    pub fn is_clear(&self) -> bool {
        *self == Trgif::Clear
    }
    #[doc = "Trigger event occurred"]
    #[inline(always)]
    pub fn is_triggered(&self) -> bool {
        *self == Trgif::Triggered
    }
}
#[doc = "Field `TRGIF` writer - Trigger interrupt flag"]
pub type TrgifW<'a, REG> = crate::BitWriter<'a, REG, Trgif>;
impl<'a, REG> TrgifW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "No trigger event occured"]
    #[inline(always)]
    pub fn clear(self) -> &'a mut crate::W<REG> {
        self.variant(Trgif::Clear)
    }
    #[doc = "Trigger event occurred"]
    #[inline(always)]
    pub fn triggered(self) -> &'a mut crate::W<REG> {
        self.variant(Trgif::Triggered)
    }
}
#[doc = "Channel 0 over capture flag"]
pub use crate::gd32e503::timer0::intf::Ch0of;
#[doc = "Field `CH0OF` reader - Channel 0 over capture flag"]
pub use crate::gd32e503::timer0::intf::Ch0ofR;
#[doc = "Field `CH1OF` reader - Channel 1 over capture flag"]
pub use crate::gd32e503::timer0::intf::Ch0ofR as Ch1ofR;
#[doc = "Field `CH2OF` reader - Channel 2 over capture flag"]
pub use crate::gd32e503::timer0::intf::Ch0ofR as Ch2ofR;
#[doc = "Field `CH3OF` reader - Channel 3 over capture flag"]
pub use crate::gd32e503::timer0::intf::Ch0ofR as Ch3ofR;
#[doc = "Field `CH0OF` writer - Channel 0 over capture flag"]
pub use crate::gd32e503::timer0::intf::Ch0ofW;
#[doc = "Field `CH1OF` writer - Channel 1 over capture flag"]
pub use crate::gd32e503::timer0::intf::Ch0ofW as Ch1ofW;
#[doc = "Field `CH2OF` writer - Channel 2 over capture flag"]
pub use crate::gd32e503::timer0::intf::Ch0ofW as Ch2ofW;
#[doc = "Field `CH3OF` writer - Channel 3 over capture flag"]
pub use crate::gd32e503::timer0::intf::Ch0ofW as Ch3ofW;
impl R {
    #[doc = "Bit 0 - Update interrupt flag"]
    #[inline(always)]
    pub fn upif(&self) -> UpifR {
        UpifR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Channel 0 capture/compare interrupt flag"]
    #[inline(always)]
    pub fn ch0if(&self) -> Ch0ifR {
        Ch0ifR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Channel 1 capture/compare interrupt flag"]
    #[inline(always)]
    pub fn ch1if(&self) -> Ch1ifR {
        Ch1ifR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Channel 2 capture/compare interrupt enable"]
    #[inline(always)]
    pub fn ch2if(&self) -> Ch2ifR {
        Ch2ifR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Channel 3 capture/compare interrupt enable"]
    #[inline(always)]
    pub fn ch3if(&self) -> Ch3ifR {
        Ch3ifR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 6 - Trigger interrupt flag"]
    #[inline(always)]
    pub fn trgif(&self) -> TrgifR {
        TrgifR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 9 - Channel 0 over capture flag"]
    #[inline(always)]
    pub fn ch0of(&self) -> Ch0ofR {
        Ch0ofR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Channel 1 over capture flag"]
    #[inline(always)]
    pub fn ch1of(&self) -> Ch1ofR {
        Ch1ofR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Channel 2 over capture flag"]
    #[inline(always)]
    pub fn ch2of(&self) -> Ch2ofR {
        Ch2ofR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Channel 3 over capture flag"]
    #[inline(always)]
    pub fn ch3of(&self) -> Ch3ofR {
        Ch3ofR::new(((self.bits >> 12) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Update interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn upif(&mut self) -> UpifW<IntfSpec> {
        UpifW::new(self, 0)
    }
    #[doc = "Bit 1 - Channel 0 capture/compare interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn ch0if(&mut self) -> Ch0ifW<IntfSpec> {
        Ch0ifW::new(self, 1)
    }
    #[doc = "Bit 2 - Channel 1 capture/compare interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn ch1if(&mut self) -> Ch1ifW<IntfSpec> {
        Ch1ifW::new(self, 2)
    }
    #[doc = "Bit 3 - Channel 2 capture/compare interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch2if(&mut self) -> Ch2ifW<IntfSpec> {
        Ch2ifW::new(self, 3)
    }
    #[doc = "Bit 4 - Channel 3 capture/compare interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch3if(&mut self) -> Ch3ifW<IntfSpec> {
        Ch3ifW::new(self, 4)
    }
    #[doc = "Bit 6 - Trigger interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn trgif(&mut self) -> TrgifW<IntfSpec> {
        TrgifW::new(self, 6)
    }
    #[doc = "Bit 9 - Channel 0 over capture flag"]
    #[inline(always)]
    #[must_use]
    pub fn ch0of(&mut self) -> Ch0ofW<IntfSpec> {
        Ch0ofW::new(self, 9)
    }
    #[doc = "Bit 10 - Channel 1 over capture flag"]
    #[inline(always)]
    #[must_use]
    pub fn ch1of(&mut self) -> Ch1ofW<IntfSpec> {
        Ch1ofW::new(self, 10)
    }
    #[doc = "Bit 11 - Channel 2 over capture flag"]
    #[inline(always)]
    #[must_use]
    pub fn ch2of(&mut self) -> Ch2ofW<IntfSpec> {
        Ch2ofW::new(self, 11)
    }
    #[doc = "Bit 12 - Channel 3 over capture flag"]
    #[inline(always)]
    #[must_use]
    pub fn ch3of(&mut self) -> Ch3ofW<IntfSpec> {
        Ch3ofW::new(self, 12)
    }
}
#[doc = "interrupt flag register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`intf::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`intf::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IntfSpec;
impl crate::RegisterSpec for IntfSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`intf::R`](R) reader structure"]
impl crate::Readable for IntfSpec {}
#[doc = "`write(|w| ..)` method takes [`intf::W`](W) writer structure"]
impl crate::Writable for IntfSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets INTF to value 0"]
impl crate::Resettable for IntfSpec {
    const RESET_VALUE: u32 = 0;
}
