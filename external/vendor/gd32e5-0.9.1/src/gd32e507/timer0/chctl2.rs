#[doc = "Register `CHCTL2` reader"]
pub type R = crate::R<Chctl2Spec>;
#[doc = "Register `CHCTL2` writer"]
pub type W = crate::W<Chctl2Spec>;
#[doc = "Channel 0 capture/compare function enable\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ch0en {
    #[doc = "0: Channel output is disabled"]
    Disabled = 0,
    #[doc = "1: Channel output is enabled"]
    Enabled = 1,
}
impl From<Ch0en> for bool {
    #[inline(always)]
    fn from(variant: Ch0en) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `CH0EN` reader - Channel 0 capture/compare function enable"]
pub type Ch0enR = crate::BitReader<Ch0en>;
impl Ch0enR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Ch0en {
        match self.bits {
            false => Ch0en::Disabled,
            true => Ch0en::Enabled,
        }
    }
    #[doc = "Channel output is disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Ch0en::Disabled
    }
    #[doc = "Channel output is enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Ch0en::Enabled
    }
}
#[doc = "Field `CH0EN` writer - Channel 0 capture/compare function enable"]
pub type Ch0enW<'a, REG> = crate::BitWriter<'a, REG, Ch0en>;
impl<'a, REG> Ch0enW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Channel output is disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0en::Disabled)
    }
    #[doc = "Channel output is enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0en::Enabled)
    }
}
#[doc = "Channel 0 capture/compare function polarity\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ch0p {
    #[doc = "0: Active high"]
    NotInverted = 0,
    #[doc = "1: Active low"]
    Inverted = 1,
}
impl From<Ch0p> for bool {
    #[inline(always)]
    fn from(variant: Ch0p) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `CH0P` reader - Channel 0 capture/compare function polarity"]
pub type Ch0pR = crate::BitReader<Ch0p>;
impl Ch0pR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Ch0p {
        match self.bits {
            false => Ch0p::NotInverted,
            true => Ch0p::Inverted,
        }
    }
    #[doc = "Active high"]
    #[inline(always)]
    pub fn is_not_inverted(&self) -> bool {
        *self == Ch0p::NotInverted
    }
    #[doc = "Active low"]
    #[inline(always)]
    pub fn is_inverted(&self) -> bool {
        *self == Ch0p::Inverted
    }
}
#[doc = "Field `CH0P` writer - Channel 0 capture/compare function polarity"]
pub type Ch0pW<'a, REG> = crate::BitWriter<'a, REG, Ch0p>;
impl<'a, REG> Ch0pW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Active high"]
    #[inline(always)]
    pub fn not_inverted(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0p::NotInverted)
    }
    #[doc = "Active low"]
    #[inline(always)]
    pub fn inverted(self) -> &'a mut crate::W<REG> {
        self.variant(Ch0p::Inverted)
    }
}
#[doc = "Field `CH0NEN` reader - Channel 0 complementary output enable"]
pub use Ch0enR as Ch0nenR;
#[doc = "Field `CH1EN` reader - Channel 1 capture/compare function enable"]
pub use Ch0enR as Ch1enR;
#[doc = "Field `CH1NEN` reader - Channel 1 complementary output enable"]
pub use Ch0enR as Ch1nenR;
#[doc = "Field `CH2EN` reader - Channel 2 capture/compare function enable"]
pub use Ch0enR as Ch2enR;
#[doc = "Field `CH2NEN` reader - Channel 2 complementary output enable"]
pub use Ch0enR as Ch2nenR;
#[doc = "Field `CH3EN` reader - Channel 3 capture/compare function enable"]
pub use Ch0enR as Ch3enR;
#[doc = "Field `CH0NEN` writer - Channel 0 complementary output enable"]
pub use Ch0enW as Ch0nenW;
#[doc = "Field `CH1EN` writer - Channel 1 capture/compare function enable"]
pub use Ch0enW as Ch1enW;
#[doc = "Field `CH1NEN` writer - Channel 1 complementary output enable"]
pub use Ch0enW as Ch1nenW;
#[doc = "Field `CH2EN` writer - Channel 2 capture/compare function enable"]
pub use Ch0enW as Ch2enW;
#[doc = "Field `CH2NEN` writer - Channel 2 complementary output enable"]
pub use Ch0enW as Ch2nenW;
#[doc = "Field `CH3EN` writer - Channel 3 capture/compare function enable"]
pub use Ch0enW as Ch3enW;
#[doc = "Field `CH0NP` reader - Channel 0 complementary output polarity"]
pub use Ch0pR as Ch0npR;
#[doc = "Field `CH1P` reader - Channel 1 capture/compare function polarity"]
pub use Ch0pR as Ch1pR;
#[doc = "Field `CH1NP` reader - Channel 1 complementary output polarity"]
pub use Ch0pR as Ch1npR;
#[doc = "Field `CH2P` reader - Channel 2 capture/compare function polarity"]
pub use Ch0pR as Ch2pR;
#[doc = "Field `CH2NP` reader - Channel 2 complementary output polarity"]
pub use Ch0pR as Ch2npR;
#[doc = "Field `CH3P` reader - Channel 3 capture/compare function polarity"]
pub use Ch0pR as Ch3pR;
#[doc = "Field `CH0NP` writer - Channel 0 complementary output polarity"]
pub use Ch0pW as Ch0npW;
#[doc = "Field `CH1P` writer - Channel 1 capture/compare function polarity"]
pub use Ch0pW as Ch1pW;
#[doc = "Field `CH1NP` writer - Channel 1 complementary output polarity"]
pub use Ch0pW as Ch1npW;
#[doc = "Field `CH2P` writer - Channel 2 capture/compare function polarity"]
pub use Ch0pW as Ch2pW;
#[doc = "Field `CH2NP` writer - Channel 2 complementary output polarity"]
pub use Ch0pW as Ch2npW;
#[doc = "Field `CH3P` writer - Channel 3 capture/compare function polarity"]
pub use Ch0pW as Ch3pW;
impl R {
    #[doc = "Bit 0 - Channel 0 capture/compare function enable"]
    #[inline(always)]
    pub fn ch0en(&self) -> Ch0enR {
        Ch0enR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Channel 0 capture/compare function polarity"]
    #[inline(always)]
    pub fn ch0p(&self) -> Ch0pR {
        Ch0pR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Channel 0 complementary output enable"]
    #[inline(always)]
    pub fn ch0nen(&self) -> Ch0nenR {
        Ch0nenR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Channel 0 complementary output polarity"]
    #[inline(always)]
    pub fn ch0np(&self) -> Ch0npR {
        Ch0npR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Channel 1 capture/compare function enable"]
    #[inline(always)]
    pub fn ch1en(&self) -> Ch1enR {
        Ch1enR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Channel 1 capture/compare function polarity"]
    #[inline(always)]
    pub fn ch1p(&self) -> Ch1pR {
        Ch1pR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Channel 1 complementary output enable"]
    #[inline(always)]
    pub fn ch1nen(&self) -> Ch1nenR {
        Ch1nenR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Channel 1 complementary output polarity"]
    #[inline(always)]
    pub fn ch1np(&self) -> Ch1npR {
        Ch1npR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Channel 2 capture/compare function enable"]
    #[inline(always)]
    pub fn ch2en(&self) -> Ch2enR {
        Ch2enR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Channel 2 capture/compare function polarity"]
    #[inline(always)]
    pub fn ch2p(&self) -> Ch2pR {
        Ch2pR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Channel 2 complementary output enable"]
    #[inline(always)]
    pub fn ch2nen(&self) -> Ch2nenR {
        Ch2nenR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Channel 2 complementary output polarity"]
    #[inline(always)]
    pub fn ch2np(&self) -> Ch2npR {
        Ch2npR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Channel 3 capture/compare function enable"]
    #[inline(always)]
    pub fn ch3en(&self) -> Ch3enR {
        Ch3enR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Channel 3 capture/compare function polarity"]
    #[inline(always)]
    pub fn ch3p(&self) -> Ch3pR {
        Ch3pR::new(((self.bits >> 13) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Channel 0 capture/compare function enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch0en(&mut self) -> Ch0enW<Chctl2Spec> {
        Ch0enW::new(self, 0)
    }
    #[doc = "Bit 1 - Channel 0 capture/compare function polarity"]
    #[inline(always)]
    #[must_use]
    pub fn ch0p(&mut self) -> Ch0pW<Chctl2Spec> {
        Ch0pW::new(self, 1)
    }
    #[doc = "Bit 2 - Channel 0 complementary output enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch0nen(&mut self) -> Ch0nenW<Chctl2Spec> {
        Ch0nenW::new(self, 2)
    }
    #[doc = "Bit 3 - Channel 0 complementary output polarity"]
    #[inline(always)]
    #[must_use]
    pub fn ch0np(&mut self) -> Ch0npW<Chctl2Spec> {
        Ch0npW::new(self, 3)
    }
    #[doc = "Bit 4 - Channel 1 capture/compare function enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch1en(&mut self) -> Ch1enW<Chctl2Spec> {
        Ch1enW::new(self, 4)
    }
    #[doc = "Bit 5 - Channel 1 capture/compare function polarity"]
    #[inline(always)]
    #[must_use]
    pub fn ch1p(&mut self) -> Ch1pW<Chctl2Spec> {
        Ch1pW::new(self, 5)
    }
    #[doc = "Bit 6 - Channel 1 complementary output enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch1nen(&mut self) -> Ch1nenW<Chctl2Spec> {
        Ch1nenW::new(self, 6)
    }
    #[doc = "Bit 7 - Channel 1 complementary output polarity"]
    #[inline(always)]
    #[must_use]
    pub fn ch1np(&mut self) -> Ch1npW<Chctl2Spec> {
        Ch1npW::new(self, 7)
    }
    #[doc = "Bit 8 - Channel 2 capture/compare function enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch2en(&mut self) -> Ch2enW<Chctl2Spec> {
        Ch2enW::new(self, 8)
    }
    #[doc = "Bit 9 - Channel 2 capture/compare function polarity"]
    #[inline(always)]
    #[must_use]
    pub fn ch2p(&mut self) -> Ch2pW<Chctl2Spec> {
        Ch2pW::new(self, 9)
    }
    #[doc = "Bit 10 - Channel 2 complementary output enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch2nen(&mut self) -> Ch2nenW<Chctl2Spec> {
        Ch2nenW::new(self, 10)
    }
    #[doc = "Bit 11 - Channel 2 complementary output polarity"]
    #[inline(always)]
    #[must_use]
    pub fn ch2np(&mut self) -> Ch2npW<Chctl2Spec> {
        Ch2npW::new(self, 11)
    }
    #[doc = "Bit 12 - Channel 3 capture/compare function enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch3en(&mut self) -> Ch3enW<Chctl2Spec> {
        Ch3enW::new(self, 12)
    }
    #[doc = "Bit 13 - Channel 3 capture/compare function polarity"]
    #[inline(always)]
    #[must_use]
    pub fn ch3p(&mut self) -> Ch3pW<Chctl2Spec> {
        Ch3pW::new(self, 13)
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
