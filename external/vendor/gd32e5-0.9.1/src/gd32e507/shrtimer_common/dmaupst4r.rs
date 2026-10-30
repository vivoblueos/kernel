#[doc = "Register `DMAUPST4R` reader"]
pub type R = crate::R<Dmaupst4rSpec>;
#[doc = "Register `DMAUPST4R` writer"]
pub type W = crate::W<Dmaupst4rSpec>;
#[doc = "Field `ST4CTL0` reader - SHRTIMER_ST4CTL0 update by DMA mode"]
pub type St4ctl0R = crate::BitReader;
#[doc = "Field `ST4CTL0` writer - SHRTIMER_ST4CTL0 update by DMA mode"]
pub type St4ctl0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4INTC` reader - SHRTIMER_ST4INTC update by DMA mode"]
pub type St4intcR = crate::BitReader;
#[doc = "Field `ST4INTC` writer - SHRTIMER_ST4INTC update by DMA mode"]
pub type St4intcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4DMAINTEN` reader - SHRTIMER_ST4DMAINTEN update by DMA mode"]
pub type St4dmaintenR = crate::BitReader;
#[doc = "Field `ST4DMAINTEN` writer - SHRTIMER_ST4DMAINTEN update by DMA mode"]
pub type St4dmaintenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4CNT` reader - SHRTIMER_ST4CNT update by DMA mode"]
pub type St4cntR = crate::BitReader;
#[doc = "Field `ST4CNT` writer - SHRTIMER_ST4CNT update by DMA mode"]
pub type St4cntW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4CAR` reader - SHRTIMER_ST4CAR update by DMA mode"]
pub type St4carR = crate::BitReader;
#[doc = "Field `ST4CAR` writer - SHRTIMER_ST4CAR update by DMA mode"]
pub type St4carW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4CREP` reader - SHRTIMER_ST4CREP update by DMA mode"]
pub type St4crepR = crate::BitReader;
#[doc = "Field `ST4CREP` writer - SHRTIMER_ST4CREP update by DMA mode"]
pub type St4crepW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4CMP0V` reader - SHRTIMER_ST4CMP0V update by DMA mode"]
pub type St4cmp0vR = crate::BitReader;
#[doc = "Field `ST4CMP0V` writer - SHRTIMER_ST4CMP0V update by DMA mode"]
pub type St4cmp0vW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4CMP1V` reader - SHRTIMER_ST4CMP1V update by DMA mode"]
pub type St4cmp1vR = crate::BitReader;
#[doc = "Field `ST4CMP1V` writer - SHRTIMER_ST4CMP1V update by DMA mode"]
pub type St4cmp1vW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4CMP2V` reader - SHRTIMER_ST4CMP2V update by DMA mode"]
pub type St4cmp2vR = crate::BitReader;
#[doc = "Field `ST4CMP2V` writer - SHRTIMER_ST4CMP2V update by DMA mode"]
pub type St4cmp2vW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4CMP3V` reader - SHRTIMER_ST4CMP3V update by DMA mode"]
pub type St4cmp3vR = crate::BitReader;
#[doc = "Field `ST4CMP3V` writer - SHRTIMER_ST4CMP3V update by DMA mode"]
pub type St4cmp3vW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4DTCTL` reader - SHRTIMER_ST4DTCTL update by DMA mode"]
pub type St4dtctlR = crate::BitReader;
#[doc = "Field `ST4DTCTL` writer - SHRTIMER_ST4DTCTL update by DMA mode"]
pub type St4dtctlW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4CH0SET` reader - SHRTIMER_ST4CH0SET update by DMA mode"]
pub type St4ch0setR = crate::BitReader;
#[doc = "Field `ST4CH0SET` writer - SHRTIMER_ST4CH0SET update by DMA mode"]
pub type St4ch0setW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4CH0RST` reader - SHRTIMER_ST4CH0RST update by DMA mode"]
pub type St4ch0rstR = crate::BitReader;
#[doc = "Field `ST4CH0RST` writer - SHRTIMER_ST4CH0RST update by DMA mode"]
pub type St4ch0rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4CH1SET` reader - SHRTIMER_ST4CH1SET update by DMA mode"]
pub type St4ch1setR = crate::BitReader;
#[doc = "Field `ST4CH1SET` writer - SHRTIMER_ST4CH1SET update by DMA mode"]
pub type St4ch1setW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4CH1RST` reader - SHRTIMER_ST4CH1RST update by DMA mode"]
pub type St4ch1rstR = crate::BitReader;
#[doc = "Field `ST4CH1RST` writer - SHRTIMER_ST4CH1RST update by DMA mode"]
pub type St4ch1rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4EXEVFCFG0` reader - SHRTIMER_ST4EXEVFCFG0update by DMA mode"]
pub type St4exevfcfg0R = crate::BitReader;
#[doc = "Field `ST4EXEVFCFG0` writer - SHRTIMER_ST4EXEVFCFG0update by DMA mode"]
pub type St4exevfcfg0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4EXEVFCFG1` reader - SHRTIMER_ST4EXEVFCFG1update by DMA mode"]
pub type St4exevfcfg1R = crate::BitReader;
#[doc = "Field `ST4EXEVFCFG1` writer - SHRTIMER_ST4EXEVFCFG1update by DMA mode"]
pub type St4exevfcfg1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4CNTRST` reader - SHRTIMER_ST4CNTRST update by DMA mode"]
pub type St4cntrstR = crate::BitReader;
#[doc = "Field `ST4CNTRST` writer - SHRTIMER_ST4CNTRST update by DMA mode"]
pub type St4cntrstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4CSCTL` reader - SHRTIMER_ST4CSCTL update by DMA mode"]
pub type St4csctlR = crate::BitReader;
#[doc = "Field `ST4CSCTL` writer - SHRTIMER_ST4CSCTL update by DMA mode"]
pub type St4csctlW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4CHOCTL` reader - SHRTIMER_ST4CHOCTL update by DMA mode"]
pub type St4choctlR = crate::BitReader;
#[doc = "Field `ST4CHOCTL` writer - SHRTIMER_ST4CHOCTL update by DMA mode"]
pub type St4choctlW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4FLTCTL` reader - SHRTIMER_ST4FLTCTL update by DMA mode"]
pub type St4fltctlR = crate::BitReader;
#[doc = "Field `ST4FLTCTL` writer - SHRTIMER_ST4FLTCTL update by DMA mode"]
pub type St4fltctlW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4ACTL` reader - SHRTIMER_ST4ACTL update by DMA mode"]
pub type St4actlR = crate::BitReader;
#[doc = "Field `ST4ACTL` writer - SHRTIMER_ST4ACTL update by DMA mode"]
pub type St4actlW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - SHRTIMER_ST4CTL0 update by DMA mode"]
    #[inline(always)]
    pub fn st4ctl0(&self) -> St4ctl0R {
        St4ctl0R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - SHRTIMER_ST4INTC update by DMA mode"]
    #[inline(always)]
    pub fn st4intc(&self) -> St4intcR {
        St4intcR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - SHRTIMER_ST4DMAINTEN update by DMA mode"]
    #[inline(always)]
    pub fn st4dmainten(&self) -> St4dmaintenR {
        St4dmaintenR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - SHRTIMER_ST4CNT update by DMA mode"]
    #[inline(always)]
    pub fn st4cnt(&self) -> St4cntR {
        St4cntR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - SHRTIMER_ST4CAR update by DMA mode"]
    #[inline(always)]
    pub fn st4car(&self) -> St4carR {
        St4carR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - SHRTIMER_ST4CREP update by DMA mode"]
    #[inline(always)]
    pub fn st4crep(&self) -> St4crepR {
        St4crepR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - SHRTIMER_ST4CMP0V update by DMA mode"]
    #[inline(always)]
    pub fn st4cmp0v(&self) -> St4cmp0vR {
        St4cmp0vR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - SHRTIMER_ST4CMP1V update by DMA mode"]
    #[inline(always)]
    pub fn st4cmp1v(&self) -> St4cmp1vR {
        St4cmp1vR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - SHRTIMER_ST4CMP2V update by DMA mode"]
    #[inline(always)]
    pub fn st4cmp2v(&self) -> St4cmp2vR {
        St4cmp2vR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - SHRTIMER_ST4CMP3V update by DMA mode"]
    #[inline(always)]
    pub fn st4cmp3v(&self) -> St4cmp3vR {
        St4cmp3vR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - SHRTIMER_ST4DTCTL update by DMA mode"]
    #[inline(always)]
    pub fn st4dtctl(&self) -> St4dtctlR {
        St4dtctlR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - SHRTIMER_ST4CH0SET update by DMA mode"]
    #[inline(always)]
    pub fn st4ch0set(&self) -> St4ch0setR {
        St4ch0setR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - SHRTIMER_ST4CH0RST update by DMA mode"]
    #[inline(always)]
    pub fn st4ch0rst(&self) -> St4ch0rstR {
        St4ch0rstR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - SHRTIMER_ST4CH1SET update by DMA mode"]
    #[inline(always)]
    pub fn st4ch1set(&self) -> St4ch1setR {
        St4ch1setR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - SHRTIMER_ST4CH1RST update by DMA mode"]
    #[inline(always)]
    pub fn st4ch1rst(&self) -> St4ch1rstR {
        St4ch1rstR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - SHRTIMER_ST4EXEVFCFG0update by DMA mode"]
    #[inline(always)]
    pub fn st4exevfcfg0(&self) -> St4exevfcfg0R {
        St4exevfcfg0R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - SHRTIMER_ST4EXEVFCFG1update by DMA mode"]
    #[inline(always)]
    pub fn st4exevfcfg1(&self) -> St4exevfcfg1R {
        St4exevfcfg1R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - SHRTIMER_ST4CNTRST update by DMA mode"]
    #[inline(always)]
    pub fn st4cntrst(&self) -> St4cntrstR {
        St4cntrstR::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - SHRTIMER_ST4CSCTL update by DMA mode"]
    #[inline(always)]
    pub fn st4csctl(&self) -> St4csctlR {
        St4csctlR::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - SHRTIMER_ST4CHOCTL update by DMA mode"]
    #[inline(always)]
    pub fn st4choctl(&self) -> St4choctlR {
        St4choctlR::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - SHRTIMER_ST4FLTCTL update by DMA mode"]
    #[inline(always)]
    pub fn st4fltctl(&self) -> St4fltctlR {
        St4fltctlR::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 31 - SHRTIMER_ST4ACTL update by DMA mode"]
    #[inline(always)]
    pub fn st4actl(&self) -> St4actlR {
        St4actlR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - SHRTIMER_ST4CTL0 update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st4ctl0(&mut self) -> St4ctl0W<Dmaupst4rSpec> {
        St4ctl0W::new(self, 0)
    }
    #[doc = "Bit 1 - SHRTIMER_ST4INTC update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st4intc(&mut self) -> St4intcW<Dmaupst4rSpec> {
        St4intcW::new(self, 1)
    }
    #[doc = "Bit 2 - SHRTIMER_ST4DMAINTEN update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st4dmainten(&mut self) -> St4dmaintenW<Dmaupst4rSpec> {
        St4dmaintenW::new(self, 2)
    }
    #[doc = "Bit 3 - SHRTIMER_ST4CNT update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st4cnt(&mut self) -> St4cntW<Dmaupst4rSpec> {
        St4cntW::new(self, 3)
    }
    #[doc = "Bit 4 - SHRTIMER_ST4CAR update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st4car(&mut self) -> St4carW<Dmaupst4rSpec> {
        St4carW::new(self, 4)
    }
    #[doc = "Bit 5 - SHRTIMER_ST4CREP update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st4crep(&mut self) -> St4crepW<Dmaupst4rSpec> {
        St4crepW::new(self, 5)
    }
    #[doc = "Bit 6 - SHRTIMER_ST4CMP0V update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st4cmp0v(&mut self) -> St4cmp0vW<Dmaupst4rSpec> {
        St4cmp0vW::new(self, 6)
    }
    #[doc = "Bit 7 - SHRTIMER_ST4CMP1V update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st4cmp1v(&mut self) -> St4cmp1vW<Dmaupst4rSpec> {
        St4cmp1vW::new(self, 7)
    }
    #[doc = "Bit 8 - SHRTIMER_ST4CMP2V update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st4cmp2v(&mut self) -> St4cmp2vW<Dmaupst4rSpec> {
        St4cmp2vW::new(self, 8)
    }
    #[doc = "Bit 9 - SHRTIMER_ST4CMP3V update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st4cmp3v(&mut self) -> St4cmp3vW<Dmaupst4rSpec> {
        St4cmp3vW::new(self, 9)
    }
    #[doc = "Bit 10 - SHRTIMER_ST4DTCTL update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st4dtctl(&mut self) -> St4dtctlW<Dmaupst4rSpec> {
        St4dtctlW::new(self, 10)
    }
    #[doc = "Bit 11 - SHRTIMER_ST4CH0SET update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st4ch0set(&mut self) -> St4ch0setW<Dmaupst4rSpec> {
        St4ch0setW::new(self, 11)
    }
    #[doc = "Bit 12 - SHRTIMER_ST4CH0RST update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st4ch0rst(&mut self) -> St4ch0rstW<Dmaupst4rSpec> {
        St4ch0rstW::new(self, 12)
    }
    #[doc = "Bit 13 - SHRTIMER_ST4CH1SET update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st4ch1set(&mut self) -> St4ch1setW<Dmaupst4rSpec> {
        St4ch1setW::new(self, 13)
    }
    #[doc = "Bit 14 - SHRTIMER_ST4CH1RST update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st4ch1rst(&mut self) -> St4ch1rstW<Dmaupst4rSpec> {
        St4ch1rstW::new(self, 14)
    }
    #[doc = "Bit 15 - SHRTIMER_ST4EXEVFCFG0update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st4exevfcfg0(&mut self) -> St4exevfcfg0W<Dmaupst4rSpec> {
        St4exevfcfg0W::new(self, 15)
    }
    #[doc = "Bit 16 - SHRTIMER_ST4EXEVFCFG1update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st4exevfcfg1(&mut self) -> St4exevfcfg1W<Dmaupst4rSpec> {
        St4exevfcfg1W::new(self, 16)
    }
    #[doc = "Bit 17 - SHRTIMER_ST4CNTRST update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st4cntrst(&mut self) -> St4cntrstW<Dmaupst4rSpec> {
        St4cntrstW::new(self, 17)
    }
    #[doc = "Bit 18 - SHRTIMER_ST4CSCTL update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st4csctl(&mut self) -> St4csctlW<Dmaupst4rSpec> {
        St4csctlW::new(self, 18)
    }
    #[doc = "Bit 19 - SHRTIMER_ST4CHOCTL update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st4choctl(&mut self) -> St4choctlW<Dmaupst4rSpec> {
        St4choctlW::new(self, 19)
    }
    #[doc = "Bit 20 - SHRTIMER_ST4FLTCTL update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st4fltctl(&mut self) -> St4fltctlW<Dmaupst4rSpec> {
        St4fltctlW::new(self, 20)
    }
    #[doc = "Bit 31 - SHRTIMER_ST4ACTL update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st4actl(&mut self) -> St4actlW<Dmaupst4rSpec> {
        St4actlW::new(self, 31)
    }
}
#[doc = "SHRTIMER DMA update Slave_TIMER4 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dmaupst4r::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dmaupst4r::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Dmaupst4rSpec;
impl crate::RegisterSpec for Dmaupst4rSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dmaupst4r::R`](R) reader structure"]
impl crate::Readable for Dmaupst4rSpec {}
#[doc = "`write(|w| ..)` method takes [`dmaupst4r::W`](W) writer structure"]
impl crate::Writable for Dmaupst4rSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DMAUPST4R to value 0"]
impl crate::Resettable for Dmaupst4rSpec {
    const RESET_VALUE: u32 = 0;
}
