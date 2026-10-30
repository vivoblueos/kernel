#[doc = "Register `ST4CHOCTL` reader"]
pub type R = crate::R<St4choctlSpec>;
#[doc = "Register `ST4CHOCTL` writer"]
pub type W = crate::W<St4choctlSpec>;
#[doc = "Field `CH0P` reader - Channel 0 output polarity"]
pub type Ch0pR = crate::BitReader;
#[doc = "Field `CH0P` writer - Channel 0 output polarity"]
pub type Ch0pW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BMCH0IEN` reader - Channel 0 IDLE state enable in bunch mode"]
pub type Bmch0ienR = crate::BitReader;
#[doc = "Field `BMCH0IEN` writer - Channel 0 IDLE state enable in bunch mode"]
pub type Bmch0ienW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ISO0` reader - Channel 0 output idle state"]
pub type Iso0R = crate::BitReader;
#[doc = "Field `ISO0` writer - Channel 0 output idle state"]
pub type Iso0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH0FLTOS` reader - Channel 0 Fault output state"]
pub type Ch0fltosR = crate::FieldReader;
#[doc = "Field `CH0FLTOS` writer - Channel 0 Fault output state"]
pub type Ch0fltosW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `CH0CSEN` reader - Channel 0 carrier-signal mode enable"]
pub type Ch0csenR = crate::BitReader;
#[doc = "Field `CH0CSEN` writer - Channel 0 carrier-signal mode enable"]
pub type Ch0csenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BMCH0DTI` reader - Channel 0 dead-time insert in bunch mode"]
pub type Bmch0dtiR = crate::BitReader;
#[doc = "Field `BMCH0DTI` writer - Channel 0 dead-time insert in bunch mode"]
pub type Bmch0dtiW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DTEN` reader - Dead time enable"]
pub type DtenR = crate::BitReader;
#[doc = "Field `DTEN` writer - Dead time enable"]
pub type DtenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DLYISMEN` reader - Delayed IDLE state mode enable"]
pub type DlyismenR = crate::BitReader;
#[doc = "Field `DLYISMEN` writer - Delayed IDLE state mode enable"]
pub type DlyismenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DLYISCH` reader - Delayed IDLE source and channel"]
pub type DlyischR = crate::FieldReader;
#[doc = "Field `DLYISCH` writer - Delayed IDLE source and channel"]
pub type DlyischW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `CH1P` reader - Channel 1 output polarity"]
pub type Ch1pR = crate::BitReader;
#[doc = "Field `CH1P` writer - Channel 1 output polarity"]
pub type Ch1pW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BMCH1IEN` reader - Channel 1 IDLE state enable in bunch mode"]
pub type Bmch1ienR = crate::BitReader;
#[doc = "Field `BMCH1IEN` writer - Channel 1 IDLE state enable in bunch mode"]
pub type Bmch1ienW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ISO1` reader - channel 1 output idle state"]
pub type Iso1R = crate::BitReader;
#[doc = "Field `ISO1` writer - channel 1 output idle state"]
pub type Iso1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH1FLTOS` reader - Channel 1 Fault output state"]
pub type Ch1fltosR = crate::FieldReader;
#[doc = "Field `CH1FLTOS` writer - Channel 1 Fault output state"]
pub type Ch1fltosW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `CH1CSEN` reader - Channel 1 carrier-signal mode enable"]
pub type Ch1csenR = crate::BitReader;
#[doc = "Field `CH1CSEN` writer - Channel 1 carrier-signal mode enable"]
pub type Ch1csenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BMCH1DTI` reader - Channel 1 dead-time insert in bunch mode"]
pub type Bmch1dtiR = crate::BitReader;
#[doc = "Field `BMCH1DTI` writer - Channel 1 dead-time insert in bunch mode"]
pub type Bmch1dtiW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 1 - Channel 0 output polarity"]
    #[inline(always)]
    pub fn ch0p(&self) -> Ch0pR {
        Ch0pR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Channel 0 IDLE state enable in bunch mode"]
    #[inline(always)]
    pub fn bmch0ien(&self) -> Bmch0ienR {
        Bmch0ienR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Channel 0 output idle state"]
    #[inline(always)]
    pub fn iso0(&self) -> Iso0R {
        Iso0R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bits 4:5 - Channel 0 Fault output state"]
    #[inline(always)]
    pub fn ch0fltos(&self) -> Ch0fltosR {
        Ch0fltosR::new(((self.bits >> 4) & 3) as u8)
    }
    #[doc = "Bit 6 - Channel 0 carrier-signal mode enable"]
    #[inline(always)]
    pub fn ch0csen(&self) -> Ch0csenR {
        Ch0csenR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Channel 0 dead-time insert in bunch mode"]
    #[inline(always)]
    pub fn bmch0dti(&self) -> Bmch0dtiR {
        Bmch0dtiR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Dead time enable"]
    #[inline(always)]
    pub fn dten(&self) -> DtenR {
        DtenR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Delayed IDLE state mode enable"]
    #[inline(always)]
    pub fn dlyismen(&self) -> DlyismenR {
        DlyismenR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bits 10:12 - Delayed IDLE source and channel"]
    #[inline(always)]
    pub fn dlyisch(&self) -> DlyischR {
        DlyischR::new(((self.bits >> 10) & 7) as u8)
    }
    #[doc = "Bit 17 - Channel 1 output polarity"]
    #[inline(always)]
    pub fn ch1p(&self) -> Ch1pR {
        Ch1pR::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - Channel 1 IDLE state enable in bunch mode"]
    #[inline(always)]
    pub fn bmch1ien(&self) -> Bmch1ienR {
        Bmch1ienR::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - channel 1 output idle state"]
    #[inline(always)]
    pub fn iso1(&self) -> Iso1R {
        Iso1R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bits 20:21 - Channel 1 Fault output state"]
    #[inline(always)]
    pub fn ch1fltos(&self) -> Ch1fltosR {
        Ch1fltosR::new(((self.bits >> 20) & 3) as u8)
    }
    #[doc = "Bit 22 - Channel 1 carrier-signal mode enable"]
    #[inline(always)]
    pub fn ch1csen(&self) -> Ch1csenR {
        Ch1csenR::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 23 - Channel 1 dead-time insert in bunch mode"]
    #[inline(always)]
    pub fn bmch1dti(&self) -> Bmch1dtiR {
        Bmch1dtiR::new(((self.bits >> 23) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 1 - Channel 0 output polarity"]
    #[inline(always)]
    #[must_use]
    pub fn ch0p(&mut self) -> Ch0pW<St4choctlSpec> {
        Ch0pW::new(self, 1)
    }
    #[doc = "Bit 2 - Channel 0 IDLE state enable in bunch mode"]
    #[inline(always)]
    #[must_use]
    pub fn bmch0ien(&mut self) -> Bmch0ienW<St4choctlSpec> {
        Bmch0ienW::new(self, 2)
    }
    #[doc = "Bit 3 - Channel 0 output idle state"]
    #[inline(always)]
    #[must_use]
    pub fn iso0(&mut self) -> Iso0W<St4choctlSpec> {
        Iso0W::new(self, 3)
    }
    #[doc = "Bits 4:5 - Channel 0 Fault output state"]
    #[inline(always)]
    #[must_use]
    pub fn ch0fltos(&mut self) -> Ch0fltosW<St4choctlSpec> {
        Ch0fltosW::new(self, 4)
    }
    #[doc = "Bit 6 - Channel 0 carrier-signal mode enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch0csen(&mut self) -> Ch0csenW<St4choctlSpec> {
        Ch0csenW::new(self, 6)
    }
    #[doc = "Bit 7 - Channel 0 dead-time insert in bunch mode"]
    #[inline(always)]
    #[must_use]
    pub fn bmch0dti(&mut self) -> Bmch0dtiW<St4choctlSpec> {
        Bmch0dtiW::new(self, 7)
    }
    #[doc = "Bit 8 - Dead time enable"]
    #[inline(always)]
    #[must_use]
    pub fn dten(&mut self) -> DtenW<St4choctlSpec> {
        DtenW::new(self, 8)
    }
    #[doc = "Bit 9 - Delayed IDLE state mode enable"]
    #[inline(always)]
    #[must_use]
    pub fn dlyismen(&mut self) -> DlyismenW<St4choctlSpec> {
        DlyismenW::new(self, 9)
    }
    #[doc = "Bits 10:12 - Delayed IDLE source and channel"]
    #[inline(always)]
    #[must_use]
    pub fn dlyisch(&mut self) -> DlyischW<St4choctlSpec> {
        DlyischW::new(self, 10)
    }
    #[doc = "Bit 17 - Channel 1 output polarity"]
    #[inline(always)]
    #[must_use]
    pub fn ch1p(&mut self) -> Ch1pW<St4choctlSpec> {
        Ch1pW::new(self, 17)
    }
    #[doc = "Bit 18 - Channel 1 IDLE state enable in bunch mode"]
    #[inline(always)]
    #[must_use]
    pub fn bmch1ien(&mut self) -> Bmch1ienW<St4choctlSpec> {
        Bmch1ienW::new(self, 18)
    }
    #[doc = "Bit 19 - channel 1 output idle state"]
    #[inline(always)]
    #[must_use]
    pub fn iso1(&mut self) -> Iso1W<St4choctlSpec> {
        Iso1W::new(self, 19)
    }
    #[doc = "Bits 20:21 - Channel 1 Fault output state"]
    #[inline(always)]
    #[must_use]
    pub fn ch1fltos(&mut self) -> Ch1fltosW<St4choctlSpec> {
        Ch1fltosW::new(self, 20)
    }
    #[doc = "Bit 22 - Channel 1 carrier-signal mode enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch1csen(&mut self) -> Ch1csenW<St4choctlSpec> {
        Ch1csenW::new(self, 22)
    }
    #[doc = "Bit 23 - Channel 1 dead-time insert in bunch mode"]
    #[inline(always)]
    #[must_use]
    pub fn bmch1dti(&mut self) -> Bmch1dtiW<St4choctlSpec> {
        Bmch1dtiW::new(self, 23)
    }
}
#[doc = "SHRTIMER Slave_TIMERx channel output control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4choctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4choctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct St4choctlSpec;
impl crate::RegisterSpec for St4choctlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`st4choctl::R`](R) reader structure"]
impl crate::Readable for St4choctlSpec {}
#[doc = "`write(|w| ..)` method takes [`st4choctl::W`](W) writer structure"]
impl crate::Writable for St4choctlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets ST4CHOCTL to value 0"]
impl crate::Resettable for St4choctlSpec {
    const RESET_VALUE: u32 = 0;
}
