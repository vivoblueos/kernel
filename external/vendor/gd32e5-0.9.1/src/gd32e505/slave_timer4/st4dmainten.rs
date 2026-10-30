#[doc = "Register `ST4DMAINTEN` reader"]
pub type R = crate::R<St4dmaintenSpec>;
#[doc = "Register `ST4DMAINTEN` writer"]
pub type W = crate::W<St4dmaintenSpec>;
#[doc = "Field `CMP0IE` reader - Compare 0 interrupt enable"]
pub type Cmp0ieR = crate::BitReader;
#[doc = "Field `CMP0IE` writer - Compare 0 interrupt enable"]
pub type Cmp0ieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMP1IE` reader - Compare 1 interrupt enable"]
pub type Cmp1ieR = crate::BitReader;
#[doc = "Field `CMP1IE` writer - Compare 1 interrupt enable"]
pub type Cmp1ieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMP2IE` reader - Compare 2 interrupt enable"]
pub type Cmp2ieR = crate::BitReader;
#[doc = "Field `CMP2IE` writer - Compare 2 interrupt enable"]
pub type Cmp2ieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMP3IE` reader - Compare 3 interrupt enable"]
pub type Cmp3ieR = crate::BitReader;
#[doc = "Field `CMP3IE` writer - Compare 3 interrupt enable"]
pub type Cmp3ieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `REPIE` reader - Repetition interrupt enable"]
pub type RepieR = crate::BitReader;
#[doc = "Field `REPIE` writer - Repetition interrupt enable"]
pub type RepieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `UPIE` reader - Update interrupt enable"]
pub type UpieR = crate::BitReader;
#[doc = "Field `UPIE` writer - Update interrupt enable"]
pub type UpieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CAP0IE` reader - Capture 0 interrupt enable"]
pub type Cap0ieR = crate::BitReader;
#[doc = "Field `CAP0IE` writer - Capture 0 interrupt enable"]
pub type Cap0ieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CAP1IE` reader - Capture 1 interrupt enable"]
pub type Cap1ieR = crate::BitReader;
#[doc = "Field `CAP1IE` writer - Capture 1 interrupt enable"]
pub type Cap1ieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH0OAIE` reader - Channel 0 output active interrupt enable"]
pub type Ch0oaieR = crate::BitReader;
#[doc = "Field `CH0OAIE` writer - Channel 0 output active interrupt enable"]
pub type Ch0oaieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH0ONAIE` reader - Channel 0 output inactive interrupt enable"]
pub type Ch0onaieR = crate::BitReader;
#[doc = "Field `CH0ONAIE` writer - Channel 0 output inactive interrupt enable"]
pub type Ch0onaieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH1OAIE` reader - Channel 1 output active interrupt enable"]
pub type Ch1oaieR = crate::BitReader;
#[doc = "Field `CH1OAIE` writer - Channel 1 output active interrupt enable"]
pub type Ch1oaieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH1ONAIE` reader - Channel 1 output inactive interrupt enable"]
pub type Ch1onaieR = crate::BitReader;
#[doc = "Field `CH1ONAIE` writer - Channel 1 output inactive interrupt enable"]
pub type Ch1onaieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RSTIE` reader - Counter reset interrupt enable"]
pub type RstieR = crate::BitReader;
#[doc = "Field `RSTIE` writer - Counter reset interrupt enable"]
pub type RstieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DLYIIE` reader - Delayed IDLE mode entry interrupt enable"]
pub type DlyiieR = crate::BitReader;
#[doc = "Field `DLYIIE` writer - Delayed IDLE mode entry interrupt enable"]
pub type DlyiieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMP0DEN` reader - Compare 0 DMA request enable"]
pub type Cmp0denR = crate::BitReader;
#[doc = "Field `CMP0DEN` writer - Compare 0 DMA request enable"]
pub type Cmp0denW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMP1DEN` reader - Compare 1 DMA request enable"]
pub type Cmp1denR = crate::BitReader;
#[doc = "Field `CMP1DEN` writer - Compare 1 DMA request enable"]
pub type Cmp1denW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMP2DEN` reader - Compare 2 DMA request enable"]
pub type Cmp2denR = crate::BitReader;
#[doc = "Field `CMP2DEN` writer - Compare 2 DMA request enable"]
pub type Cmp2denW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMP3DEN` reader - Compare 3 DMA request enable"]
pub type Cmp3denR = crate::BitReader;
#[doc = "Field `CMP3DEN` writer - Compare 3 DMA request enable"]
pub type Cmp3denW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `REPDEN` reader - Repetition DMA request enable"]
pub type RepdenR = crate::BitReader;
#[doc = "Field `REPDEN` writer - Repetition DMA request enable"]
pub type RepdenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `UPDEN` reader - Update DMA request enable"]
pub type UpdenR = crate::BitReader;
#[doc = "Field `UPDEN` writer - Update DMA request enable"]
pub type UpdenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CAP0DEN` reader - Capture 0 DMA request enable"]
pub type Cap0denR = crate::BitReader;
#[doc = "Field `CAP0DEN` writer - Capture 0 DMA request enable"]
pub type Cap0denW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CAP1DEN` reader - Capture 1 DMA request enable"]
pub type Cap1denR = crate::BitReader;
#[doc = "Field `CAP1DEN` writer - Capture 1 DMA request enable"]
pub type Cap1denW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH0ADEN` reader - Channel 0 output active DMA request enable"]
pub type Ch0adenR = crate::BitReader;
#[doc = "Field `CH0ADEN` writer - Channel 0 output active DMA request enable"]
pub type Ch0adenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH0ONADEN` reader - Channel 0 output inactive DMA request enable"]
pub type Ch0onadenR = crate::BitReader;
#[doc = "Field `CH0ONADEN` writer - Channel 0 output inactive DMA request enable"]
pub type Ch0onadenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH1OADEN` reader - Channel 1 output active DMA request enable"]
pub type Ch1oadenR = crate::BitReader;
#[doc = "Field `CH1OADEN` writer - Channel 1 output active DMA request enable"]
pub type Ch1oadenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CH1ONADEN` reader - Channel 1 output inactive DMA request enable"]
pub type Ch1onadenR = crate::BitReader;
#[doc = "Field `CH1ONADEN` writer - Channel 1 output inactive DMA request enable"]
pub type Ch1onadenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RSTDEN` reader - Counter reset DMA request enable"]
pub type RstdenR = crate::BitReader;
#[doc = "Field `RSTDEN` writer - Counter reset DMA request enable"]
pub type RstdenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DLYIDEN` reader - Delayed IDLE mode entry DMA request enable"]
pub type DlyidenR = crate::BitReader;
#[doc = "Field `DLYIDEN` writer - Delayed IDLE mode entry DMA request enable"]
pub type DlyidenW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Compare 0 interrupt enable"]
    #[inline(always)]
    pub fn cmp0ie(&self) -> Cmp0ieR {
        Cmp0ieR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Compare 1 interrupt enable"]
    #[inline(always)]
    pub fn cmp1ie(&self) -> Cmp1ieR {
        Cmp1ieR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Compare 2 interrupt enable"]
    #[inline(always)]
    pub fn cmp2ie(&self) -> Cmp2ieR {
        Cmp2ieR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Compare 3 interrupt enable"]
    #[inline(always)]
    pub fn cmp3ie(&self) -> Cmp3ieR {
        Cmp3ieR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Repetition interrupt enable"]
    #[inline(always)]
    pub fn repie(&self) -> RepieR {
        RepieR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 6 - Update interrupt enable"]
    #[inline(always)]
    pub fn upie(&self) -> UpieR {
        UpieR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Capture 0 interrupt enable"]
    #[inline(always)]
    pub fn cap0ie(&self) -> Cap0ieR {
        Cap0ieR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Capture 1 interrupt enable"]
    #[inline(always)]
    pub fn cap1ie(&self) -> Cap1ieR {
        Cap1ieR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Channel 0 output active interrupt enable"]
    #[inline(always)]
    pub fn ch0oaie(&self) -> Ch0oaieR {
        Ch0oaieR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Channel 0 output inactive interrupt enable"]
    #[inline(always)]
    pub fn ch0onaie(&self) -> Ch0onaieR {
        Ch0onaieR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Channel 1 output active interrupt enable"]
    #[inline(always)]
    pub fn ch1oaie(&self) -> Ch1oaieR {
        Ch1oaieR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Channel 1 output inactive interrupt enable"]
    #[inline(always)]
    pub fn ch1onaie(&self) -> Ch1onaieR {
        Ch1onaieR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Counter reset interrupt enable"]
    #[inline(always)]
    pub fn rstie(&self) -> RstieR {
        RstieR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Delayed IDLE mode entry interrupt enable"]
    #[inline(always)]
    pub fn dlyiie(&self) -> DlyiieR {
        DlyiieR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 16 - Compare 0 DMA request enable"]
    #[inline(always)]
    pub fn cmp0den(&self) -> Cmp0denR {
        Cmp0denR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - Compare 1 DMA request enable"]
    #[inline(always)]
    pub fn cmp1den(&self) -> Cmp1denR {
        Cmp1denR::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - Compare 2 DMA request enable"]
    #[inline(always)]
    pub fn cmp2den(&self) -> Cmp2denR {
        Cmp2denR::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - Compare 3 DMA request enable"]
    #[inline(always)]
    pub fn cmp3den(&self) -> Cmp3denR {
        Cmp3denR::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - Repetition DMA request enable"]
    #[inline(always)]
    pub fn repden(&self) -> RepdenR {
        RepdenR::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 22 - Update DMA request enable"]
    #[inline(always)]
    pub fn upden(&self) -> UpdenR {
        UpdenR::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 23 - Capture 0 DMA request enable"]
    #[inline(always)]
    pub fn cap0den(&self) -> Cap0denR {
        Cap0denR::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bit 24 - Capture 1 DMA request enable"]
    #[inline(always)]
    pub fn cap1den(&self) -> Cap1denR {
        Cap1denR::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - Channel 0 output active DMA request enable"]
    #[inline(always)]
    pub fn ch0aden(&self) -> Ch0adenR {
        Ch0adenR::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - Channel 0 output inactive DMA request enable"]
    #[inline(always)]
    pub fn ch0onaden(&self) -> Ch0onadenR {
        Ch0onadenR::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - Channel 1 output active DMA request enable"]
    #[inline(always)]
    pub fn ch1oaden(&self) -> Ch1oadenR {
        Ch1oadenR::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - Channel 1 output inactive DMA request enable"]
    #[inline(always)]
    pub fn ch1onaden(&self) -> Ch1onadenR {
        Ch1onadenR::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - Counter reset DMA request enable"]
    #[inline(always)]
    pub fn rstden(&self) -> RstdenR {
        RstdenR::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - Delayed IDLE mode entry DMA request enable"]
    #[inline(always)]
    pub fn dlyiden(&self) -> DlyidenR {
        DlyidenR::new(((self.bits >> 30) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Compare 0 interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn cmp0ie(&mut self) -> Cmp0ieW<St4dmaintenSpec> {
        Cmp0ieW::new(self, 0)
    }
    #[doc = "Bit 1 - Compare 1 interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn cmp1ie(&mut self) -> Cmp1ieW<St4dmaintenSpec> {
        Cmp1ieW::new(self, 1)
    }
    #[doc = "Bit 2 - Compare 2 interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn cmp2ie(&mut self) -> Cmp2ieW<St4dmaintenSpec> {
        Cmp2ieW::new(self, 2)
    }
    #[doc = "Bit 3 - Compare 3 interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn cmp3ie(&mut self) -> Cmp3ieW<St4dmaintenSpec> {
        Cmp3ieW::new(self, 3)
    }
    #[doc = "Bit 4 - Repetition interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn repie(&mut self) -> RepieW<St4dmaintenSpec> {
        RepieW::new(self, 4)
    }
    #[doc = "Bit 6 - Update interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn upie(&mut self) -> UpieW<St4dmaintenSpec> {
        UpieW::new(self, 6)
    }
    #[doc = "Bit 7 - Capture 0 interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn cap0ie(&mut self) -> Cap0ieW<St4dmaintenSpec> {
        Cap0ieW::new(self, 7)
    }
    #[doc = "Bit 8 - Capture 1 interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn cap1ie(&mut self) -> Cap1ieW<St4dmaintenSpec> {
        Cap1ieW::new(self, 8)
    }
    #[doc = "Bit 9 - Channel 0 output active interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch0oaie(&mut self) -> Ch0oaieW<St4dmaintenSpec> {
        Ch0oaieW::new(self, 9)
    }
    #[doc = "Bit 10 - Channel 0 output inactive interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch0onaie(&mut self) -> Ch0onaieW<St4dmaintenSpec> {
        Ch0onaieW::new(self, 10)
    }
    #[doc = "Bit 11 - Channel 1 output active interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch1oaie(&mut self) -> Ch1oaieW<St4dmaintenSpec> {
        Ch1oaieW::new(self, 11)
    }
    #[doc = "Bit 12 - Channel 1 output inactive interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch1onaie(&mut self) -> Ch1onaieW<St4dmaintenSpec> {
        Ch1onaieW::new(self, 12)
    }
    #[doc = "Bit 13 - Counter reset interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn rstie(&mut self) -> RstieW<St4dmaintenSpec> {
        RstieW::new(self, 13)
    }
    #[doc = "Bit 14 - Delayed IDLE mode entry interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn dlyiie(&mut self) -> DlyiieW<St4dmaintenSpec> {
        DlyiieW::new(self, 14)
    }
    #[doc = "Bit 16 - Compare 0 DMA request enable"]
    #[inline(always)]
    #[must_use]
    pub fn cmp0den(&mut self) -> Cmp0denW<St4dmaintenSpec> {
        Cmp0denW::new(self, 16)
    }
    #[doc = "Bit 17 - Compare 1 DMA request enable"]
    #[inline(always)]
    #[must_use]
    pub fn cmp1den(&mut self) -> Cmp1denW<St4dmaintenSpec> {
        Cmp1denW::new(self, 17)
    }
    #[doc = "Bit 18 - Compare 2 DMA request enable"]
    #[inline(always)]
    #[must_use]
    pub fn cmp2den(&mut self) -> Cmp2denW<St4dmaintenSpec> {
        Cmp2denW::new(self, 18)
    }
    #[doc = "Bit 19 - Compare 3 DMA request enable"]
    #[inline(always)]
    #[must_use]
    pub fn cmp3den(&mut self) -> Cmp3denW<St4dmaintenSpec> {
        Cmp3denW::new(self, 19)
    }
    #[doc = "Bit 20 - Repetition DMA request enable"]
    #[inline(always)]
    #[must_use]
    pub fn repden(&mut self) -> RepdenW<St4dmaintenSpec> {
        RepdenW::new(self, 20)
    }
    #[doc = "Bit 22 - Update DMA request enable"]
    #[inline(always)]
    #[must_use]
    pub fn upden(&mut self) -> UpdenW<St4dmaintenSpec> {
        UpdenW::new(self, 22)
    }
    #[doc = "Bit 23 - Capture 0 DMA request enable"]
    #[inline(always)]
    #[must_use]
    pub fn cap0den(&mut self) -> Cap0denW<St4dmaintenSpec> {
        Cap0denW::new(self, 23)
    }
    #[doc = "Bit 24 - Capture 1 DMA request enable"]
    #[inline(always)]
    #[must_use]
    pub fn cap1den(&mut self) -> Cap1denW<St4dmaintenSpec> {
        Cap1denW::new(self, 24)
    }
    #[doc = "Bit 25 - Channel 0 output active DMA request enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch0aden(&mut self) -> Ch0adenW<St4dmaintenSpec> {
        Ch0adenW::new(self, 25)
    }
    #[doc = "Bit 26 - Channel 0 output inactive DMA request enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch0onaden(&mut self) -> Ch0onadenW<St4dmaintenSpec> {
        Ch0onadenW::new(self, 26)
    }
    #[doc = "Bit 27 - Channel 1 output active DMA request enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch1oaden(&mut self) -> Ch1oadenW<St4dmaintenSpec> {
        Ch1oadenW::new(self, 27)
    }
    #[doc = "Bit 28 - Channel 1 output inactive DMA request enable"]
    #[inline(always)]
    #[must_use]
    pub fn ch1onaden(&mut self) -> Ch1onadenW<St4dmaintenSpec> {
        Ch1onadenW::new(self, 28)
    }
    #[doc = "Bit 29 - Counter reset DMA request enable"]
    #[inline(always)]
    #[must_use]
    pub fn rstden(&mut self) -> RstdenW<St4dmaintenSpec> {
        RstdenW::new(self, 29)
    }
    #[doc = "Bit 30 - Delayed IDLE mode entry DMA request enable"]
    #[inline(always)]
    #[must_use]
    pub fn dlyiden(&mut self) -> DlyidenW<St4dmaintenSpec> {
        DlyidenW::new(self, 30)
    }
}
#[doc = "SHRTIMER Slave_TIMERx DMA and interrupt enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st4dmainten::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st4dmainten::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct St4dmaintenSpec;
impl crate::RegisterSpec for St4dmaintenSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`st4dmainten::R`](R) reader structure"]
impl crate::Readable for St4dmaintenSpec {}
#[doc = "`write(|w| ..)` method takes [`st4dmainten::W`](W) writer structure"]
impl crate::Writable for St4dmaintenSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets ST4DMAINTEN to value 0"]
impl crate::Resettable for St4dmaintenSpec {
    const RESET_VALUE: u32 = 0;
}
