#[doc = "Register `DMAUPST2R` reader"]
pub type R = crate::R<Dmaupst2rSpec>;
#[doc = "Register `DMAUPST2R` writer"]
pub type W = crate::W<Dmaupst2rSpec>;
#[doc = "Field `ST2CTL0` reader - SHRTIMER_ST2CTL0 update by DMA mode"]
pub type St2ctl0R = crate::BitReader;
#[doc = "Field `ST2CTL0` writer - SHRTIMER_ST2CTL0 update by DMA mode"]
pub type St2ctl0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2INTC` reader - SHRTIMER_ST2INTC update by DMA mode"]
pub type St2intcR = crate::BitReader;
#[doc = "Field `ST2INTC` writer - SHRTIMER_ST2INTC update by DMA mode"]
pub type St2intcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2DMAINTEN` reader - SHRTIMER_ST2DMAINTEN update by DMA mode"]
pub type St2dmaintenR = crate::BitReader;
#[doc = "Field `ST2DMAINTEN` writer - SHRTIMER_ST2DMAINTEN update by DMA mode"]
pub type St2dmaintenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2CNT` reader - SHRTIMER_ST2CNT update by DMA mode"]
pub type St2cntR = crate::BitReader;
#[doc = "Field `ST2CNT` writer - SHRTIMER_ST2CNT update by DMA mode"]
pub type St2cntW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2CAR` reader - SHRTIMER_ST2CAR update by DMA mode"]
pub type St2carR = crate::BitReader;
#[doc = "Field `ST2CAR` writer - SHRTIMER_ST2CAR update by DMA mode"]
pub type St2carW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2CREP` reader - SHRTIMER_ST2CREP update by DMA mode"]
pub type St2crepR = crate::BitReader;
#[doc = "Field `ST2CREP` writer - SHRTIMER_ST2CREP update by DMA mode"]
pub type St2crepW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2CMP0V` reader - SHRTIMER_ST2CMP0V update by DMA mode"]
pub type St2cmp0vR = crate::BitReader;
#[doc = "Field `ST2CMP0V` writer - SHRTIMER_ST2CMP0V update by DMA mode"]
pub type St2cmp0vW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2CMP1V` reader - SHRTIMER_ST2CMP1V update by DMA mode"]
pub type St2cmp1vR = crate::BitReader;
#[doc = "Field `ST2CMP1V` writer - SHRTIMER_ST2CMP1V update by DMA mode"]
pub type St2cmp1vW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2CMP2V` reader - SHRTIMER_ST2CMP2V update by DMA mode"]
pub type St2cmp2vR = crate::BitReader;
#[doc = "Field `ST2CMP2V` writer - SHRTIMER_ST2CMP2V update by DMA mode"]
pub type St2cmp2vW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2CMP3V` reader - SHRTIMER_ST2CMP3V update by DMA mode"]
pub type St2cmp3vR = crate::BitReader;
#[doc = "Field `ST2CMP3V` writer - SHRTIMER_ST2CMP3V update by DMA mode"]
pub type St2cmp3vW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2DTCTL` reader - SHRTIMER_ST2DTCTL update by DMA mode"]
pub type St2dtctlR = crate::BitReader;
#[doc = "Field `ST2DTCTL` writer - SHRTIMER_ST2DTCTL update by DMA mode"]
pub type St2dtctlW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2CH0SET` reader - SHRTIMER_ST2CH0SET update by DMA mode"]
pub type St2ch0setR = crate::BitReader;
#[doc = "Field `ST2CH0SET` writer - SHRTIMER_ST2CH0SET update by DMA mode"]
pub type St2ch0setW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2CH0RST` reader - SHRTIMER_ST2CH0RST update by DMA mode"]
pub type St2ch0rstR = crate::BitReader;
#[doc = "Field `ST2CH0RST` writer - SHRTIMER_ST2CH0RST update by DMA mode"]
pub type St2ch0rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2CH1SET` reader - SHRTIMER_ST2CH1SET update by DMA mode"]
pub type St2ch1setR = crate::BitReader;
#[doc = "Field `ST2CH1SET` writer - SHRTIMER_ST2CH1SET update by DMA mode"]
pub type St2ch1setW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2CH1RST` reader - SHRTIMER_ST2CH1RST update by DMA mode"]
pub type St2ch1rstR = crate::BitReader;
#[doc = "Field `ST2CH1RST` writer - SHRTIMER_ST2CH1RST update by DMA mode"]
pub type St2ch1rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2EXEVFCFG0` reader - SHRTIMER_ST2EXEVFCFG0update by DMA mode"]
pub type St2exevfcfg0R = crate::BitReader;
#[doc = "Field `ST2EXEVFCFG0` writer - SHRTIMER_ST2EXEVFCFG0update by DMA mode"]
pub type St2exevfcfg0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2EXEVFCFG1` reader - SHRTIMER_ST2EXEVFCFG1update by DMA mode"]
pub type St2exevfcfg1R = crate::BitReader;
#[doc = "Field `ST2EXEVFCFG1` writer - SHRTIMER_ST2EXEVFCFG1update by DMA mode"]
pub type St2exevfcfg1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2CNTRST` reader - SHRTIMER_ST2CNTRST update by DMA mode"]
pub type St2cntrstR = crate::BitReader;
#[doc = "Field `ST2CNTRST` writer - SHRTIMER_ST2CNTRST update by DMA mode"]
pub type St2cntrstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2CSCTL` reader - SHRTIMER_ST2CSCTL update by DMA mode"]
pub type St2csctlR = crate::BitReader;
#[doc = "Field `ST2CSCTL` writer - SHRTIMER_ST2CSCTL update by DMA mode"]
pub type St2csctlW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2CHOCTL` reader - SHRTIMER_ST2CHOCTL update by DMA mode"]
pub type St2choctlR = crate::BitReader;
#[doc = "Field `ST2CHOCTL` writer - SHRTIMER_ST2CHOCTL update by DMA mode"]
pub type St2choctlW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2FLTCTL` reader - SHRTIMER_ST2FLTCTL update by DMA mode"]
pub type St2fltctlR = crate::BitReader;
#[doc = "Field `ST2FLTCTL` writer - SHRTIMER_ST2FLTCTL update by DMA mode"]
pub type St2fltctlW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2ACTL` reader - SHRTIMER_ST2ACTL update by DMA mode"]
pub type St2actlR = crate::BitReader;
#[doc = "Field `ST2ACTL` writer - SHRTIMER_ST2ACTL update by DMA mode"]
pub type St2actlW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - SHRTIMER_ST2CTL0 update by DMA mode"]
    #[inline(always)]
    pub fn st2ctl0(&self) -> St2ctl0R {
        St2ctl0R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - SHRTIMER_ST2INTC update by DMA mode"]
    #[inline(always)]
    pub fn st2intc(&self) -> St2intcR {
        St2intcR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - SHRTIMER_ST2DMAINTEN update by DMA mode"]
    #[inline(always)]
    pub fn st2dmainten(&self) -> St2dmaintenR {
        St2dmaintenR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - SHRTIMER_ST2CNT update by DMA mode"]
    #[inline(always)]
    pub fn st2cnt(&self) -> St2cntR {
        St2cntR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - SHRTIMER_ST2CAR update by DMA mode"]
    #[inline(always)]
    pub fn st2car(&self) -> St2carR {
        St2carR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - SHRTIMER_ST2CREP update by DMA mode"]
    #[inline(always)]
    pub fn st2crep(&self) -> St2crepR {
        St2crepR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - SHRTIMER_ST2CMP0V update by DMA mode"]
    #[inline(always)]
    pub fn st2cmp0v(&self) -> St2cmp0vR {
        St2cmp0vR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - SHRTIMER_ST2CMP1V update by DMA mode"]
    #[inline(always)]
    pub fn st2cmp1v(&self) -> St2cmp1vR {
        St2cmp1vR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - SHRTIMER_ST2CMP2V update by DMA mode"]
    #[inline(always)]
    pub fn st2cmp2v(&self) -> St2cmp2vR {
        St2cmp2vR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - SHRTIMER_ST2CMP3V update by DMA mode"]
    #[inline(always)]
    pub fn st2cmp3v(&self) -> St2cmp3vR {
        St2cmp3vR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - SHRTIMER_ST2DTCTL update by DMA mode"]
    #[inline(always)]
    pub fn st2dtctl(&self) -> St2dtctlR {
        St2dtctlR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - SHRTIMER_ST2CH0SET update by DMA mode"]
    #[inline(always)]
    pub fn st2ch0set(&self) -> St2ch0setR {
        St2ch0setR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - SHRTIMER_ST2CH0RST update by DMA mode"]
    #[inline(always)]
    pub fn st2ch0rst(&self) -> St2ch0rstR {
        St2ch0rstR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - SHRTIMER_ST2CH1SET update by DMA mode"]
    #[inline(always)]
    pub fn st2ch1set(&self) -> St2ch1setR {
        St2ch1setR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - SHRTIMER_ST2CH1RST update by DMA mode"]
    #[inline(always)]
    pub fn st2ch1rst(&self) -> St2ch1rstR {
        St2ch1rstR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - SHRTIMER_ST2EXEVFCFG0update by DMA mode"]
    #[inline(always)]
    pub fn st2exevfcfg0(&self) -> St2exevfcfg0R {
        St2exevfcfg0R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - SHRTIMER_ST2EXEVFCFG1update by DMA mode"]
    #[inline(always)]
    pub fn st2exevfcfg1(&self) -> St2exevfcfg1R {
        St2exevfcfg1R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - SHRTIMER_ST2CNTRST update by DMA mode"]
    #[inline(always)]
    pub fn st2cntrst(&self) -> St2cntrstR {
        St2cntrstR::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - SHRTIMER_ST2CSCTL update by DMA mode"]
    #[inline(always)]
    pub fn st2csctl(&self) -> St2csctlR {
        St2csctlR::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - SHRTIMER_ST2CHOCTL update by DMA mode"]
    #[inline(always)]
    pub fn st2choctl(&self) -> St2choctlR {
        St2choctlR::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - SHRTIMER_ST2FLTCTL update by DMA mode"]
    #[inline(always)]
    pub fn st2fltctl(&self) -> St2fltctlR {
        St2fltctlR::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 31 - SHRTIMER_ST2ACTL update by DMA mode"]
    #[inline(always)]
    pub fn st2actl(&self) -> St2actlR {
        St2actlR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - SHRTIMER_ST2CTL0 update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st2ctl0(&mut self) -> St2ctl0W<Dmaupst2rSpec> {
        St2ctl0W::new(self, 0)
    }
    #[doc = "Bit 1 - SHRTIMER_ST2INTC update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st2intc(&mut self) -> St2intcW<Dmaupst2rSpec> {
        St2intcW::new(self, 1)
    }
    #[doc = "Bit 2 - SHRTIMER_ST2DMAINTEN update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st2dmainten(&mut self) -> St2dmaintenW<Dmaupst2rSpec> {
        St2dmaintenW::new(self, 2)
    }
    #[doc = "Bit 3 - SHRTIMER_ST2CNT update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st2cnt(&mut self) -> St2cntW<Dmaupst2rSpec> {
        St2cntW::new(self, 3)
    }
    #[doc = "Bit 4 - SHRTIMER_ST2CAR update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st2car(&mut self) -> St2carW<Dmaupst2rSpec> {
        St2carW::new(self, 4)
    }
    #[doc = "Bit 5 - SHRTIMER_ST2CREP update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st2crep(&mut self) -> St2crepW<Dmaupst2rSpec> {
        St2crepW::new(self, 5)
    }
    #[doc = "Bit 6 - SHRTIMER_ST2CMP0V update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st2cmp0v(&mut self) -> St2cmp0vW<Dmaupst2rSpec> {
        St2cmp0vW::new(self, 6)
    }
    #[doc = "Bit 7 - SHRTIMER_ST2CMP1V update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st2cmp1v(&mut self) -> St2cmp1vW<Dmaupst2rSpec> {
        St2cmp1vW::new(self, 7)
    }
    #[doc = "Bit 8 - SHRTIMER_ST2CMP2V update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st2cmp2v(&mut self) -> St2cmp2vW<Dmaupst2rSpec> {
        St2cmp2vW::new(self, 8)
    }
    #[doc = "Bit 9 - SHRTIMER_ST2CMP3V update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st2cmp3v(&mut self) -> St2cmp3vW<Dmaupst2rSpec> {
        St2cmp3vW::new(self, 9)
    }
    #[doc = "Bit 10 - SHRTIMER_ST2DTCTL update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st2dtctl(&mut self) -> St2dtctlW<Dmaupst2rSpec> {
        St2dtctlW::new(self, 10)
    }
    #[doc = "Bit 11 - SHRTIMER_ST2CH0SET update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st2ch0set(&mut self) -> St2ch0setW<Dmaupst2rSpec> {
        St2ch0setW::new(self, 11)
    }
    #[doc = "Bit 12 - SHRTIMER_ST2CH0RST update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st2ch0rst(&mut self) -> St2ch0rstW<Dmaupst2rSpec> {
        St2ch0rstW::new(self, 12)
    }
    #[doc = "Bit 13 - SHRTIMER_ST2CH1SET update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st2ch1set(&mut self) -> St2ch1setW<Dmaupst2rSpec> {
        St2ch1setW::new(self, 13)
    }
    #[doc = "Bit 14 - SHRTIMER_ST2CH1RST update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st2ch1rst(&mut self) -> St2ch1rstW<Dmaupst2rSpec> {
        St2ch1rstW::new(self, 14)
    }
    #[doc = "Bit 15 - SHRTIMER_ST2EXEVFCFG0update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st2exevfcfg0(&mut self) -> St2exevfcfg0W<Dmaupst2rSpec> {
        St2exevfcfg0W::new(self, 15)
    }
    #[doc = "Bit 16 - SHRTIMER_ST2EXEVFCFG1update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st2exevfcfg1(&mut self) -> St2exevfcfg1W<Dmaupst2rSpec> {
        St2exevfcfg1W::new(self, 16)
    }
    #[doc = "Bit 17 - SHRTIMER_ST2CNTRST update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st2cntrst(&mut self) -> St2cntrstW<Dmaupst2rSpec> {
        St2cntrstW::new(self, 17)
    }
    #[doc = "Bit 18 - SHRTIMER_ST2CSCTL update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st2csctl(&mut self) -> St2csctlW<Dmaupst2rSpec> {
        St2csctlW::new(self, 18)
    }
    #[doc = "Bit 19 - SHRTIMER_ST2CHOCTL update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st2choctl(&mut self) -> St2choctlW<Dmaupst2rSpec> {
        St2choctlW::new(self, 19)
    }
    #[doc = "Bit 20 - SHRTIMER_ST2FLTCTL update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st2fltctl(&mut self) -> St2fltctlW<Dmaupst2rSpec> {
        St2fltctlW::new(self, 20)
    }
    #[doc = "Bit 31 - SHRTIMER_ST2ACTL update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st2actl(&mut self) -> St2actlW<Dmaupst2rSpec> {
        St2actlW::new(self, 31)
    }
}
#[doc = "SHRTIMER DMA update Slave_TIMER2 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dmaupst2r::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dmaupst2r::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Dmaupst2rSpec;
impl crate::RegisterSpec for Dmaupst2rSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dmaupst2r::R`](R) reader structure"]
impl crate::Readable for Dmaupst2rSpec {}
#[doc = "`write(|w| ..)` method takes [`dmaupst2r::W`](W) writer structure"]
impl crate::Writable for Dmaupst2rSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DMAUPST2R to value 0"]
impl crate::Resettable for Dmaupst2rSpec {
    const RESET_VALUE: u32 = 0;
}
