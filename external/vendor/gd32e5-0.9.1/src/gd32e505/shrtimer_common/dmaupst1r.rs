#[doc = "Register `DMAUPST1R` reader"]
pub type R = crate::R<Dmaupst1rSpec>;
#[doc = "Register `DMAUPST1R` writer"]
pub type W = crate::W<Dmaupst1rSpec>;
#[doc = "Field `ST1CTL0` reader - SHRTIMER_ST1CTL0 update by DMA mode"]
pub type St1ctl0R = crate::BitReader;
#[doc = "Field `ST1CTL0` writer - SHRTIMER_ST1CTL0 update by DMA mode"]
pub type St1ctl0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1INTC` reader - SHRTIMER_ST1INTC update by DMA mode"]
pub type St1intcR = crate::BitReader;
#[doc = "Field `ST1INTC` writer - SHRTIMER_ST1INTC update by DMA mode"]
pub type St1intcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1DMAINTEN` reader - SHRTIMER_ST1DMAINTEN update by DMA mode"]
pub type St1dmaintenR = crate::BitReader;
#[doc = "Field `ST1DMAINTEN` writer - SHRTIMER_ST1DMAINTEN update by DMA mode"]
pub type St1dmaintenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1CNT` reader - SHRTIMER_ST1CNT update by DMA mode"]
pub type St1cntR = crate::BitReader;
#[doc = "Field `ST1CNT` writer - SHRTIMER_ST1CNT update by DMA mode"]
pub type St1cntW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1CAR` reader - SHRTIMER_ST1CAR update by DMA mode"]
pub type St1carR = crate::BitReader;
#[doc = "Field `ST1CAR` writer - SHRTIMER_ST1CAR update by DMA mode"]
pub type St1carW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1CREP` reader - SHRTIMER_ST1CREP update by DMA mode"]
pub type St1crepR = crate::BitReader;
#[doc = "Field `ST1CREP` writer - SHRTIMER_ST1CREP update by DMA mode"]
pub type St1crepW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1CMP0V` reader - SHRTIMER_ST1CMP0V update by DMA mode"]
pub type St1cmp0vR = crate::BitReader;
#[doc = "Field `ST1CMP0V` writer - SHRTIMER_ST1CMP0V update by DMA mode"]
pub type St1cmp0vW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1CMP1V` reader - SHRTIMER_ST1CMP1V update by DMA mode"]
pub type St1cmp1vR = crate::BitReader;
#[doc = "Field `ST1CMP1V` writer - SHRTIMER_ST1CMP1V update by DMA mode"]
pub type St1cmp1vW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1CMP2V` reader - SHRTIMER_ST1CMP2V update by DMA mode"]
pub type St1cmp2vR = crate::BitReader;
#[doc = "Field `ST1CMP2V` writer - SHRTIMER_ST1CMP2V update by DMA mode"]
pub type St1cmp2vW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1CMP3V` reader - SHRTIMER_ST1CMP3V update by DMA mode"]
pub type St1cmp3vR = crate::BitReader;
#[doc = "Field `ST1CMP3V` writer - SHRTIMER_ST1CMP3V update by DMA mode"]
pub type St1cmp3vW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1DTCTL` reader - SHRTIMER_ST1DTCTL update by DMA mode"]
pub type St1dtctlR = crate::BitReader;
#[doc = "Field `ST1DTCTL` writer - SHRTIMER_ST1DTCTL update by DMA mode"]
pub type St1dtctlW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1CH0SET` reader - SHRTIMER_ST1CH0SET update by DMA mode"]
pub type St1ch0setR = crate::BitReader;
#[doc = "Field `ST1CH0SET` writer - SHRTIMER_ST1CH0SET update by DMA mode"]
pub type St1ch0setW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1CH0RST` reader - SHRTIMER_ST1CH0RST update by DMA mode"]
pub type St1ch0rstR = crate::BitReader;
#[doc = "Field `ST1CH0RST` writer - SHRTIMER_ST1CH0RST update by DMA mode"]
pub type St1ch0rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1CH1SET` reader - SHRTIMER_ST1CH1SET update by DMA mode"]
pub type St1ch1setR = crate::BitReader;
#[doc = "Field `ST1CH1SET` writer - SHRTIMER_ST1CH1SET update by DMA mode"]
pub type St1ch1setW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1CH1RST` reader - SHRTIMER_ST1CH1RST update by DMA mode"]
pub type St1ch1rstR = crate::BitReader;
#[doc = "Field `ST1CH1RST` writer - SHRTIMER_ST1CH1RST update by DMA mode"]
pub type St1ch1rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1EXEVFCFG0` reader - SHRTIMER_ST1EXEVFCFG0update by DMA mode"]
pub type St1exevfcfg0R = crate::BitReader;
#[doc = "Field `ST1EXEVFCFG0` writer - SHRTIMER_ST1EXEVFCFG0update by DMA mode"]
pub type St1exevfcfg0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1EXEVFCFG1` reader - SHRTIMER_ST1EXEVFCFG1update by DMA mode"]
pub type St1exevfcfg1R = crate::BitReader;
#[doc = "Field `ST1EXEVFCFG1` writer - SHRTIMER_ST1EXEVFCFG1update by DMA mode"]
pub type St1exevfcfg1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1CNTRST` reader - SHRTIMER_ST1CNTRST update by DMA mode"]
pub type St1cntrstR = crate::BitReader;
#[doc = "Field `ST1CNTRST` writer - SHRTIMER_ST1CNTRST update by DMA mode"]
pub type St1cntrstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1CSCTL` reader - SHRTIMER_ST1CSCTL update by DMA mode"]
pub type St1csctlR = crate::BitReader;
#[doc = "Field `ST1CSCTL` writer - SHRTIMER_ST1CSCTL update by DMA mode"]
pub type St1csctlW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1CHOCTL` reader - SHRTIMER_ST1CHOCTL update by DMA mode"]
pub type St1choctlR = crate::BitReader;
#[doc = "Field `ST1CHOCTL` writer - SHRTIMER_ST1CHOCTL update by DMA mode"]
pub type St1choctlW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1FLTCTL` reader - SHRTIMER_ST1FLTCTL update by DMA mode"]
pub type St1fltctlR = crate::BitReader;
#[doc = "Field `ST1FLTCTL` writer - SHRTIMER_ST1FLTCTL update by DMA mode"]
pub type St1fltctlW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1ACTL` reader - SHRTIMER_ST1ACTL update by DMA mode"]
pub type St1actlR = crate::BitReader;
#[doc = "Field `ST1ACTL` writer - SHRTIMER_ST1ACTL update by DMA mode"]
pub type St1actlW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - SHRTIMER_ST1CTL0 update by DMA mode"]
    #[inline(always)]
    pub fn st1ctl0(&self) -> St1ctl0R {
        St1ctl0R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - SHRTIMER_ST1INTC update by DMA mode"]
    #[inline(always)]
    pub fn st1intc(&self) -> St1intcR {
        St1intcR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - SHRTIMER_ST1DMAINTEN update by DMA mode"]
    #[inline(always)]
    pub fn st1dmainten(&self) -> St1dmaintenR {
        St1dmaintenR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - SHRTIMER_ST1CNT update by DMA mode"]
    #[inline(always)]
    pub fn st1cnt(&self) -> St1cntR {
        St1cntR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - SHRTIMER_ST1CAR update by DMA mode"]
    #[inline(always)]
    pub fn st1car(&self) -> St1carR {
        St1carR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - SHRTIMER_ST1CREP update by DMA mode"]
    #[inline(always)]
    pub fn st1crep(&self) -> St1crepR {
        St1crepR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - SHRTIMER_ST1CMP0V update by DMA mode"]
    #[inline(always)]
    pub fn st1cmp0v(&self) -> St1cmp0vR {
        St1cmp0vR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - SHRTIMER_ST1CMP1V update by DMA mode"]
    #[inline(always)]
    pub fn st1cmp1v(&self) -> St1cmp1vR {
        St1cmp1vR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - SHRTIMER_ST1CMP2V update by DMA mode"]
    #[inline(always)]
    pub fn st1cmp2v(&self) -> St1cmp2vR {
        St1cmp2vR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - SHRTIMER_ST1CMP3V update by DMA mode"]
    #[inline(always)]
    pub fn st1cmp3v(&self) -> St1cmp3vR {
        St1cmp3vR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - SHRTIMER_ST1DTCTL update by DMA mode"]
    #[inline(always)]
    pub fn st1dtctl(&self) -> St1dtctlR {
        St1dtctlR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - SHRTIMER_ST1CH0SET update by DMA mode"]
    #[inline(always)]
    pub fn st1ch0set(&self) -> St1ch0setR {
        St1ch0setR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - SHRTIMER_ST1CH0RST update by DMA mode"]
    #[inline(always)]
    pub fn st1ch0rst(&self) -> St1ch0rstR {
        St1ch0rstR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - SHRTIMER_ST1CH1SET update by DMA mode"]
    #[inline(always)]
    pub fn st1ch1set(&self) -> St1ch1setR {
        St1ch1setR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - SHRTIMER_ST1CH1RST update by DMA mode"]
    #[inline(always)]
    pub fn st1ch1rst(&self) -> St1ch1rstR {
        St1ch1rstR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - SHRTIMER_ST1EXEVFCFG0update by DMA mode"]
    #[inline(always)]
    pub fn st1exevfcfg0(&self) -> St1exevfcfg0R {
        St1exevfcfg0R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - SHRTIMER_ST1EXEVFCFG1update by DMA mode"]
    #[inline(always)]
    pub fn st1exevfcfg1(&self) -> St1exevfcfg1R {
        St1exevfcfg1R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - SHRTIMER_ST1CNTRST update by DMA mode"]
    #[inline(always)]
    pub fn st1cntrst(&self) -> St1cntrstR {
        St1cntrstR::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - SHRTIMER_ST1CSCTL update by DMA mode"]
    #[inline(always)]
    pub fn st1csctl(&self) -> St1csctlR {
        St1csctlR::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - SHRTIMER_ST1CHOCTL update by DMA mode"]
    #[inline(always)]
    pub fn st1choctl(&self) -> St1choctlR {
        St1choctlR::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - SHRTIMER_ST1FLTCTL update by DMA mode"]
    #[inline(always)]
    pub fn st1fltctl(&self) -> St1fltctlR {
        St1fltctlR::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 31 - SHRTIMER_ST1ACTL update by DMA mode"]
    #[inline(always)]
    pub fn st1actl(&self) -> St1actlR {
        St1actlR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - SHRTIMER_ST1CTL0 update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st1ctl0(&mut self) -> St1ctl0W<Dmaupst1rSpec> {
        St1ctl0W::new(self, 0)
    }
    #[doc = "Bit 1 - SHRTIMER_ST1INTC update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st1intc(&mut self) -> St1intcW<Dmaupst1rSpec> {
        St1intcW::new(self, 1)
    }
    #[doc = "Bit 2 - SHRTIMER_ST1DMAINTEN update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st1dmainten(&mut self) -> St1dmaintenW<Dmaupst1rSpec> {
        St1dmaintenW::new(self, 2)
    }
    #[doc = "Bit 3 - SHRTIMER_ST1CNT update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st1cnt(&mut self) -> St1cntW<Dmaupst1rSpec> {
        St1cntW::new(self, 3)
    }
    #[doc = "Bit 4 - SHRTIMER_ST1CAR update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st1car(&mut self) -> St1carW<Dmaupst1rSpec> {
        St1carW::new(self, 4)
    }
    #[doc = "Bit 5 - SHRTIMER_ST1CREP update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st1crep(&mut self) -> St1crepW<Dmaupst1rSpec> {
        St1crepW::new(self, 5)
    }
    #[doc = "Bit 6 - SHRTIMER_ST1CMP0V update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st1cmp0v(&mut self) -> St1cmp0vW<Dmaupst1rSpec> {
        St1cmp0vW::new(self, 6)
    }
    #[doc = "Bit 7 - SHRTIMER_ST1CMP1V update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st1cmp1v(&mut self) -> St1cmp1vW<Dmaupst1rSpec> {
        St1cmp1vW::new(self, 7)
    }
    #[doc = "Bit 8 - SHRTIMER_ST1CMP2V update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st1cmp2v(&mut self) -> St1cmp2vW<Dmaupst1rSpec> {
        St1cmp2vW::new(self, 8)
    }
    #[doc = "Bit 9 - SHRTIMER_ST1CMP3V update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st1cmp3v(&mut self) -> St1cmp3vW<Dmaupst1rSpec> {
        St1cmp3vW::new(self, 9)
    }
    #[doc = "Bit 10 - SHRTIMER_ST1DTCTL update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st1dtctl(&mut self) -> St1dtctlW<Dmaupst1rSpec> {
        St1dtctlW::new(self, 10)
    }
    #[doc = "Bit 11 - SHRTIMER_ST1CH0SET update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st1ch0set(&mut self) -> St1ch0setW<Dmaupst1rSpec> {
        St1ch0setW::new(self, 11)
    }
    #[doc = "Bit 12 - SHRTIMER_ST1CH0RST update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st1ch0rst(&mut self) -> St1ch0rstW<Dmaupst1rSpec> {
        St1ch0rstW::new(self, 12)
    }
    #[doc = "Bit 13 - SHRTIMER_ST1CH1SET update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st1ch1set(&mut self) -> St1ch1setW<Dmaupst1rSpec> {
        St1ch1setW::new(self, 13)
    }
    #[doc = "Bit 14 - SHRTIMER_ST1CH1RST update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st1ch1rst(&mut self) -> St1ch1rstW<Dmaupst1rSpec> {
        St1ch1rstW::new(self, 14)
    }
    #[doc = "Bit 15 - SHRTIMER_ST1EXEVFCFG0update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st1exevfcfg0(&mut self) -> St1exevfcfg0W<Dmaupst1rSpec> {
        St1exevfcfg0W::new(self, 15)
    }
    #[doc = "Bit 16 - SHRTIMER_ST1EXEVFCFG1update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st1exevfcfg1(&mut self) -> St1exevfcfg1W<Dmaupst1rSpec> {
        St1exevfcfg1W::new(self, 16)
    }
    #[doc = "Bit 17 - SHRTIMER_ST1CNTRST update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st1cntrst(&mut self) -> St1cntrstW<Dmaupst1rSpec> {
        St1cntrstW::new(self, 17)
    }
    #[doc = "Bit 18 - SHRTIMER_ST1CSCTL update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st1csctl(&mut self) -> St1csctlW<Dmaupst1rSpec> {
        St1csctlW::new(self, 18)
    }
    #[doc = "Bit 19 - SHRTIMER_ST1CHOCTL update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st1choctl(&mut self) -> St1choctlW<Dmaupst1rSpec> {
        St1choctlW::new(self, 19)
    }
    #[doc = "Bit 20 - SHRTIMER_ST1FLTCTL update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st1fltctl(&mut self) -> St1fltctlW<Dmaupst1rSpec> {
        St1fltctlW::new(self, 20)
    }
    #[doc = "Bit 31 - SHRTIMER_ST1ACTL update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st1actl(&mut self) -> St1actlW<Dmaupst1rSpec> {
        St1actlW::new(self, 31)
    }
}
#[doc = "SHRTIMER DMA update Slave_TIMER1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dmaupst1r::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dmaupst1r::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Dmaupst1rSpec;
impl crate::RegisterSpec for Dmaupst1rSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dmaupst1r::R`](R) reader structure"]
impl crate::Readable for Dmaupst1rSpec {}
#[doc = "`write(|w| ..)` method takes [`dmaupst1r::W`](W) writer structure"]
impl crate::Writable for Dmaupst1rSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DMAUPST1R to value 0"]
impl crate::Resettable for Dmaupst1rSpec {
    const RESET_VALUE: u32 = 0;
}
