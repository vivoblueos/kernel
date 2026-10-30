#[doc = "Register `DMAUPST0R` reader"]
pub type R = crate::R<Dmaupst0rSpec>;
#[doc = "Register `DMAUPST0R` writer"]
pub type W = crate::W<Dmaupst0rSpec>;
#[doc = "Field `ST0CTL0` reader - SHRTIMER_ST0CTL0 update by DMA mode"]
pub type St0ctl0R = crate::BitReader;
#[doc = "Field `ST0CTL0` writer - SHRTIMER_ST0CTL0 update by DMA mode"]
pub type St0ctl0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0INTC` reader - SHRTIMER_ST0INTC update by DMA mode"]
pub type St0intcR = crate::BitReader;
#[doc = "Field `ST0INTC` writer - SHRTIMER_ST0INTC update by DMA mode"]
pub type St0intcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0DMAINTEN` reader - SHRTIMER_ST0DMAINTEN update by DMA mode"]
pub type St0dmaintenR = crate::BitReader;
#[doc = "Field `ST0DMAINTEN` writer - SHRTIMER_ST0DMAINTEN update by DMA mode"]
pub type St0dmaintenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0CNT` reader - SHRTIMER_ST0CNT update by DMA mode"]
pub type St0cntR = crate::BitReader;
#[doc = "Field `ST0CNT` writer - SHRTIMER_ST0CNT update by DMA mode"]
pub type St0cntW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0CAR` reader - SHRTIMER_ST0CAR update by DMA mode"]
pub type St0carR = crate::BitReader;
#[doc = "Field `ST0CAR` writer - SHRTIMER_ST0CAR update by DMA mode"]
pub type St0carW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0CREP` reader - SHRTIMER_ST0CREP update by DMA mode"]
pub type St0crepR = crate::BitReader;
#[doc = "Field `ST0CREP` writer - SHRTIMER_ST0CREP update by DMA mode"]
pub type St0crepW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0CMP0V` reader - SHRTIMER_ST0CMP0V update by DMA mode"]
pub type St0cmp0vR = crate::BitReader;
#[doc = "Field `ST0CMP0V` writer - SHRTIMER_ST0CMP0V update by DMA mode"]
pub type St0cmp0vW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0CMP1V` reader - SHRTIMER_ST0CMP1V update by DMA mode"]
pub type St0cmp1vR = crate::BitReader;
#[doc = "Field `ST0CMP1V` writer - SHRTIMER_ST0CMP1V update by DMA mode"]
pub type St0cmp1vW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0CMP2V` reader - SHRTIMER_ST0CMP2V update by DMA mode"]
pub type St0cmp2vR = crate::BitReader;
#[doc = "Field `ST0CMP2V` writer - SHRTIMER_ST0CMP2V update by DMA mode"]
pub type St0cmp2vW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0CMP3V` reader - SHRTIMER_ST0CMP3V update by DMA mode"]
pub type St0cmp3vR = crate::BitReader;
#[doc = "Field `ST0CMP3V` writer - SHRTIMER_ST0CMP3V update by DMA mode"]
pub type St0cmp3vW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0DTCTL` reader - SHRTIMER_ST0DTCTL update by DMA mode"]
pub type St0dtctlR = crate::BitReader;
#[doc = "Field `ST0DTCTL` writer - SHRTIMER_ST0DTCTL update by DMA mode"]
pub type St0dtctlW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0CH0SET` reader - SHRTIMER_ST0CH0SET update by DMA mode"]
pub type St0ch0setR = crate::BitReader;
#[doc = "Field `ST0CH0SET` writer - SHRTIMER_ST0CH0SET update by DMA mode"]
pub type St0ch0setW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0CH0RST` reader - SHRTIMER_ST0CH0RST update by DMA mode"]
pub type St0ch0rstR = crate::BitReader;
#[doc = "Field `ST0CH0RST` writer - SHRTIMER_ST0CH0RST update by DMA mode"]
pub type St0ch0rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0CH1SET` reader - SHRTIMER_ST0CH1SET update by DMA mode"]
pub type St0ch1setR = crate::BitReader;
#[doc = "Field `ST0CH1SET` writer - SHRTIMER_ST0CH1SET update by DMA mode"]
pub type St0ch1setW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0CH1RST` reader - SHRTIMER_ST0CH1RST update by DMA mode"]
pub type St0ch1rstR = crate::BitReader;
#[doc = "Field `ST0CH1RST` writer - SHRTIMER_ST0CH1RST update by DMA mode"]
pub type St0ch1rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0EXEVFCFG0` reader - SHRTIMER_ST0EXEVFCFG0update by DMA mode"]
pub type St0exevfcfg0R = crate::BitReader;
#[doc = "Field `ST0EXEVFCFG0` writer - SHRTIMER_ST0EXEVFCFG0update by DMA mode"]
pub type St0exevfcfg0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0EXEVFCFG1` reader - SHRTIMER_ST0EXEVFCFG1update by DMA mode"]
pub type St0exevfcfg1R = crate::BitReader;
#[doc = "Field `ST0EXEVFCFG1` writer - SHRTIMER_ST0EXEVFCFG1update by DMA mode"]
pub type St0exevfcfg1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0CNTRST` reader - SHRTIMER_ST0CNTRST update by DMA mode"]
pub type St0cntrstR = crate::BitReader;
#[doc = "Field `ST0CNTRST` writer - SHRTIMER_ST0CNTRST update by DMA mode"]
pub type St0cntrstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0CSCTL` reader - SHRTIMER_ST0CSCTL update by DMA mode"]
pub type St0csctlR = crate::BitReader;
#[doc = "Field `ST0CSCTL` writer - SHRTIMER_ST0CSCTL update by DMA mode"]
pub type St0csctlW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0CHOCTL` reader - SHRTIMER_ST0CHOCTL update by DMA mode"]
pub type St0choctlR = crate::BitReader;
#[doc = "Field `ST0CHOCTL` writer - SHRTIMER_ST0CHOCTL update by DMA mode"]
pub type St0choctlW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0FLTCTL` reader - SHRTIMER_ST0FLTCTL update by DMA mode"]
pub type St0fltctlR = crate::BitReader;
#[doc = "Field `ST0FLTCTL` writer - SHRTIMER_ST0FLTCTL update by DMA mode"]
pub type St0fltctlW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0ACTL` reader - SHRTIMER_ST0ACTL update by DMA mode"]
pub type St0actlR = crate::BitReader;
#[doc = "Field `ST0ACTL` writer - SHRTIMER_ST0ACTL update by DMA mode"]
pub type St0actlW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - SHRTIMER_ST0CTL0 update by DMA mode"]
    #[inline(always)]
    pub fn st0ctl0(&self) -> St0ctl0R {
        St0ctl0R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - SHRTIMER_ST0INTC update by DMA mode"]
    #[inline(always)]
    pub fn st0intc(&self) -> St0intcR {
        St0intcR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - SHRTIMER_ST0DMAINTEN update by DMA mode"]
    #[inline(always)]
    pub fn st0dmainten(&self) -> St0dmaintenR {
        St0dmaintenR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - SHRTIMER_ST0CNT update by DMA mode"]
    #[inline(always)]
    pub fn st0cnt(&self) -> St0cntR {
        St0cntR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - SHRTIMER_ST0CAR update by DMA mode"]
    #[inline(always)]
    pub fn st0car(&self) -> St0carR {
        St0carR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - SHRTIMER_ST0CREP update by DMA mode"]
    #[inline(always)]
    pub fn st0crep(&self) -> St0crepR {
        St0crepR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - SHRTIMER_ST0CMP0V update by DMA mode"]
    #[inline(always)]
    pub fn st0cmp0v(&self) -> St0cmp0vR {
        St0cmp0vR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - SHRTIMER_ST0CMP1V update by DMA mode"]
    #[inline(always)]
    pub fn st0cmp1v(&self) -> St0cmp1vR {
        St0cmp1vR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - SHRTIMER_ST0CMP2V update by DMA mode"]
    #[inline(always)]
    pub fn st0cmp2v(&self) -> St0cmp2vR {
        St0cmp2vR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - SHRTIMER_ST0CMP3V update by DMA mode"]
    #[inline(always)]
    pub fn st0cmp3v(&self) -> St0cmp3vR {
        St0cmp3vR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - SHRTIMER_ST0DTCTL update by DMA mode"]
    #[inline(always)]
    pub fn st0dtctl(&self) -> St0dtctlR {
        St0dtctlR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - SHRTIMER_ST0CH0SET update by DMA mode"]
    #[inline(always)]
    pub fn st0ch0set(&self) -> St0ch0setR {
        St0ch0setR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - SHRTIMER_ST0CH0RST update by DMA mode"]
    #[inline(always)]
    pub fn st0ch0rst(&self) -> St0ch0rstR {
        St0ch0rstR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - SHRTIMER_ST0CH1SET update by DMA mode"]
    #[inline(always)]
    pub fn st0ch1set(&self) -> St0ch1setR {
        St0ch1setR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - SHRTIMER_ST0CH1RST update by DMA mode"]
    #[inline(always)]
    pub fn st0ch1rst(&self) -> St0ch1rstR {
        St0ch1rstR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - SHRTIMER_ST0EXEVFCFG0update by DMA mode"]
    #[inline(always)]
    pub fn st0exevfcfg0(&self) -> St0exevfcfg0R {
        St0exevfcfg0R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - SHRTIMER_ST0EXEVFCFG1update by DMA mode"]
    #[inline(always)]
    pub fn st0exevfcfg1(&self) -> St0exevfcfg1R {
        St0exevfcfg1R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - SHRTIMER_ST0CNTRST update by DMA mode"]
    #[inline(always)]
    pub fn st0cntrst(&self) -> St0cntrstR {
        St0cntrstR::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - SHRTIMER_ST0CSCTL update by DMA mode"]
    #[inline(always)]
    pub fn st0csctl(&self) -> St0csctlR {
        St0csctlR::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - SHRTIMER_ST0CHOCTL update by DMA mode"]
    #[inline(always)]
    pub fn st0choctl(&self) -> St0choctlR {
        St0choctlR::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - SHRTIMER_ST0FLTCTL update by DMA mode"]
    #[inline(always)]
    pub fn st0fltctl(&self) -> St0fltctlR {
        St0fltctlR::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 31 - SHRTIMER_ST0ACTL update by DMA mode"]
    #[inline(always)]
    pub fn st0actl(&self) -> St0actlR {
        St0actlR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - SHRTIMER_ST0CTL0 update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st0ctl0(&mut self) -> St0ctl0W<Dmaupst0rSpec> {
        St0ctl0W::new(self, 0)
    }
    #[doc = "Bit 1 - SHRTIMER_ST0INTC update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st0intc(&mut self) -> St0intcW<Dmaupst0rSpec> {
        St0intcW::new(self, 1)
    }
    #[doc = "Bit 2 - SHRTIMER_ST0DMAINTEN update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st0dmainten(&mut self) -> St0dmaintenW<Dmaupst0rSpec> {
        St0dmaintenW::new(self, 2)
    }
    #[doc = "Bit 3 - SHRTIMER_ST0CNT update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st0cnt(&mut self) -> St0cntW<Dmaupst0rSpec> {
        St0cntW::new(self, 3)
    }
    #[doc = "Bit 4 - SHRTIMER_ST0CAR update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st0car(&mut self) -> St0carW<Dmaupst0rSpec> {
        St0carW::new(self, 4)
    }
    #[doc = "Bit 5 - SHRTIMER_ST0CREP update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st0crep(&mut self) -> St0crepW<Dmaupst0rSpec> {
        St0crepW::new(self, 5)
    }
    #[doc = "Bit 6 - SHRTIMER_ST0CMP0V update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st0cmp0v(&mut self) -> St0cmp0vW<Dmaupst0rSpec> {
        St0cmp0vW::new(self, 6)
    }
    #[doc = "Bit 7 - SHRTIMER_ST0CMP1V update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st0cmp1v(&mut self) -> St0cmp1vW<Dmaupst0rSpec> {
        St0cmp1vW::new(self, 7)
    }
    #[doc = "Bit 8 - SHRTIMER_ST0CMP2V update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st0cmp2v(&mut self) -> St0cmp2vW<Dmaupst0rSpec> {
        St0cmp2vW::new(self, 8)
    }
    #[doc = "Bit 9 - SHRTIMER_ST0CMP3V update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st0cmp3v(&mut self) -> St0cmp3vW<Dmaupst0rSpec> {
        St0cmp3vW::new(self, 9)
    }
    #[doc = "Bit 10 - SHRTIMER_ST0DTCTL update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st0dtctl(&mut self) -> St0dtctlW<Dmaupst0rSpec> {
        St0dtctlW::new(self, 10)
    }
    #[doc = "Bit 11 - SHRTIMER_ST0CH0SET update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st0ch0set(&mut self) -> St0ch0setW<Dmaupst0rSpec> {
        St0ch0setW::new(self, 11)
    }
    #[doc = "Bit 12 - SHRTIMER_ST0CH0RST update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st0ch0rst(&mut self) -> St0ch0rstW<Dmaupst0rSpec> {
        St0ch0rstW::new(self, 12)
    }
    #[doc = "Bit 13 - SHRTIMER_ST0CH1SET update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st0ch1set(&mut self) -> St0ch1setW<Dmaupst0rSpec> {
        St0ch1setW::new(self, 13)
    }
    #[doc = "Bit 14 - SHRTIMER_ST0CH1RST update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st0ch1rst(&mut self) -> St0ch1rstW<Dmaupst0rSpec> {
        St0ch1rstW::new(self, 14)
    }
    #[doc = "Bit 15 - SHRTIMER_ST0EXEVFCFG0update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st0exevfcfg0(&mut self) -> St0exevfcfg0W<Dmaupst0rSpec> {
        St0exevfcfg0W::new(self, 15)
    }
    #[doc = "Bit 16 - SHRTIMER_ST0EXEVFCFG1update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st0exevfcfg1(&mut self) -> St0exevfcfg1W<Dmaupst0rSpec> {
        St0exevfcfg1W::new(self, 16)
    }
    #[doc = "Bit 17 - SHRTIMER_ST0CNTRST update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st0cntrst(&mut self) -> St0cntrstW<Dmaupst0rSpec> {
        St0cntrstW::new(self, 17)
    }
    #[doc = "Bit 18 - SHRTIMER_ST0CSCTL update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st0csctl(&mut self) -> St0csctlW<Dmaupst0rSpec> {
        St0csctlW::new(self, 18)
    }
    #[doc = "Bit 19 - SHRTIMER_ST0CHOCTL update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st0choctl(&mut self) -> St0choctlW<Dmaupst0rSpec> {
        St0choctlW::new(self, 19)
    }
    #[doc = "Bit 20 - SHRTIMER_ST0FLTCTL update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st0fltctl(&mut self) -> St0fltctlW<Dmaupst0rSpec> {
        St0fltctlW::new(self, 20)
    }
    #[doc = "Bit 31 - SHRTIMER_ST0ACTL update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st0actl(&mut self) -> St0actlW<Dmaupst0rSpec> {
        St0actlW::new(self, 31)
    }
}
#[doc = "SHRTIMER DMA update Slave_TIMER0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dmaupst0r::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dmaupst0r::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Dmaupst0rSpec;
impl crate::RegisterSpec for Dmaupst0rSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dmaupst0r::R`](R) reader structure"]
impl crate::Readable for Dmaupst0rSpec {}
#[doc = "`write(|w| ..)` method takes [`dmaupst0r::W`](W) writer structure"]
impl crate::Writable for Dmaupst0rSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DMAUPST0R to value 0"]
impl crate::Resettable for Dmaupst0rSpec {
    const RESET_VALUE: u32 = 0;
}
