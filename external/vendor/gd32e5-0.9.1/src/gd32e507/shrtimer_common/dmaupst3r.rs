#[doc = "Register `DMAUPST3R` reader"]
pub type R = crate::R<Dmaupst3rSpec>;
#[doc = "Register `DMAUPST3R` writer"]
pub type W = crate::W<Dmaupst3rSpec>;
#[doc = "Field `ST3CTL0` reader - SHRTIMER_ST3CTL0 update by DMA mode"]
pub type St3ctl0R = crate::BitReader;
#[doc = "Field `ST3CTL0` writer - SHRTIMER_ST3CTL0 update by DMA mode"]
pub type St3ctl0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3INTC` reader - SHRTIMER_ST3INTC update by DMA mode"]
pub type St3intcR = crate::BitReader;
#[doc = "Field `ST3INTC` writer - SHRTIMER_ST3INTC update by DMA mode"]
pub type St3intcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3DMAINTEN` reader - SHRTIMER_ST3DMAINTEN update by DMA mode"]
pub type St3dmaintenR = crate::BitReader;
#[doc = "Field `ST3DMAINTEN` writer - SHRTIMER_ST3DMAINTEN update by DMA mode"]
pub type St3dmaintenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3CNT` reader - SHRTIMER_ST3CNT update by DMA mode"]
pub type St3cntR = crate::BitReader;
#[doc = "Field `ST3CNT` writer - SHRTIMER_ST3CNT update by DMA mode"]
pub type St3cntW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3CAR` reader - SHRTIMER_ST3CAR update by DMA mode"]
pub type St3carR = crate::BitReader;
#[doc = "Field `ST3CAR` writer - SHRTIMER_ST3CAR update by DMA mode"]
pub type St3carW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3CREP` reader - SHRTIMER_ST3CREP update by DMA mode"]
pub type St3crepR = crate::BitReader;
#[doc = "Field `ST3CREP` writer - SHRTIMER_ST3CREP update by DMA mode"]
pub type St3crepW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3CMP0V` reader - SHRTIMER_ST3CMP0V update by DMA mode"]
pub type St3cmp0vR = crate::BitReader;
#[doc = "Field `ST3CMP0V` writer - SHRTIMER_ST3CMP0V update by DMA mode"]
pub type St3cmp0vW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3CMP1V` reader - SHRTIMER_ST3CMP1V update by DMA mode"]
pub type St3cmp1vR = crate::BitReader;
#[doc = "Field `ST3CMP1V` writer - SHRTIMER_ST3CMP1V update by DMA mode"]
pub type St3cmp1vW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3CMP2V` reader - SHRTIMER_ST3CMP2V update by DMA mode"]
pub type St3cmp2vR = crate::BitReader;
#[doc = "Field `ST3CMP2V` writer - SHRTIMER_ST3CMP2V update by DMA mode"]
pub type St3cmp2vW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3CMP3V` reader - SHRTIMER_ST3CMP3V update by DMA mode"]
pub type St3cmp3vR = crate::BitReader;
#[doc = "Field `ST3CMP3V` writer - SHRTIMER_ST3CMP3V update by DMA mode"]
pub type St3cmp3vW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3DTCTL` reader - SHRTIMER_ST3DTCTL update by DMA mode"]
pub type St3dtctlR = crate::BitReader;
#[doc = "Field `ST3DTCTL` writer - SHRTIMER_ST3DTCTL update by DMA mode"]
pub type St3dtctlW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3CH0SET` reader - SHRTIMER_ST3CH0SET update by DMA mode"]
pub type St3ch0setR = crate::BitReader;
#[doc = "Field `ST3CH0SET` writer - SHRTIMER_ST3CH0SET update by DMA mode"]
pub type St3ch0setW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3CH0RST` reader - SHRTIMER_ST3CH0RST update by DMA mode"]
pub type St3ch0rstR = crate::BitReader;
#[doc = "Field `ST3CH0RST` writer - SHRTIMER_ST3CH0RST update by DMA mode"]
pub type St3ch0rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3CH1SET` reader - SHRTIMER_ST3CH1SET update by DMA mode"]
pub type St3ch1setR = crate::BitReader;
#[doc = "Field `ST3CH1SET` writer - SHRTIMER_ST3CH1SET update by DMA mode"]
pub type St3ch1setW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3CH1RST` reader - SHRTIMER_ST3CH1RST update by DMA mode"]
pub type St3ch1rstR = crate::BitReader;
#[doc = "Field `ST3CH1RST` writer - SHRTIMER_ST3CH1RST update by DMA mode"]
pub type St3ch1rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3EXEVFCFG0` reader - SHRTIMER_ST3EXEVFCFG0update by DMA mode"]
pub type St3exevfcfg0R = crate::BitReader;
#[doc = "Field `ST3EXEVFCFG0` writer - SHRTIMER_ST3EXEVFCFG0update by DMA mode"]
pub type St3exevfcfg0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3EXEVFCFG1` reader - SHRTIMER_ST3EXEVFCFG1update by DMA mode"]
pub type St3exevfcfg1R = crate::BitReader;
#[doc = "Field `ST3EXEVFCFG1` writer - SHRTIMER_ST3EXEVFCFG1update by DMA mode"]
pub type St3exevfcfg1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3CNTRST` reader - SHRTIMER_ST3CNTRST update by DMA mode"]
pub type St3cntrstR = crate::BitReader;
#[doc = "Field `ST3CNTRST` writer - SHRTIMER_ST3CNTRST update by DMA mode"]
pub type St3cntrstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3CSCTL` reader - SHRTIMER_ST3CSCTL update by DMA mode"]
pub type St3csctlR = crate::BitReader;
#[doc = "Field `ST3CSCTL` writer - SHRTIMER_ST3CSCTL update by DMA mode"]
pub type St3csctlW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3CHOCTL` reader - SHRTIMER_ST3CHOCTL update by DMA mode"]
pub type St3choctlR = crate::BitReader;
#[doc = "Field `ST3CHOCTL` writer - SHRTIMER_ST3CHOCTL update by DMA mode"]
pub type St3choctlW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3FLTCTL` reader - SHRTIMER_ST3FLTCTL update by DMA mode"]
pub type St3fltctlR = crate::BitReader;
#[doc = "Field `ST3FLTCTL` writer - SHRTIMER_ST3FLTCTL update by DMA mode"]
pub type St3fltctlW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3ACTL` reader - SHRTIMER_ST3ACTL update by DMA mode"]
pub type St3actlR = crate::BitReader;
#[doc = "Field `ST3ACTL` writer - SHRTIMER_ST3ACTL update by DMA mode"]
pub type St3actlW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - SHRTIMER_ST3CTL0 update by DMA mode"]
    #[inline(always)]
    pub fn st3ctl0(&self) -> St3ctl0R {
        St3ctl0R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - SHRTIMER_ST3INTC update by DMA mode"]
    #[inline(always)]
    pub fn st3intc(&self) -> St3intcR {
        St3intcR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - SHRTIMER_ST3DMAINTEN update by DMA mode"]
    #[inline(always)]
    pub fn st3dmainten(&self) -> St3dmaintenR {
        St3dmaintenR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - SHRTIMER_ST3CNT update by DMA mode"]
    #[inline(always)]
    pub fn st3cnt(&self) -> St3cntR {
        St3cntR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - SHRTIMER_ST3CAR update by DMA mode"]
    #[inline(always)]
    pub fn st3car(&self) -> St3carR {
        St3carR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - SHRTIMER_ST3CREP update by DMA mode"]
    #[inline(always)]
    pub fn st3crep(&self) -> St3crepR {
        St3crepR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - SHRTIMER_ST3CMP0V update by DMA mode"]
    #[inline(always)]
    pub fn st3cmp0v(&self) -> St3cmp0vR {
        St3cmp0vR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - SHRTIMER_ST3CMP1V update by DMA mode"]
    #[inline(always)]
    pub fn st3cmp1v(&self) -> St3cmp1vR {
        St3cmp1vR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - SHRTIMER_ST3CMP2V update by DMA mode"]
    #[inline(always)]
    pub fn st3cmp2v(&self) -> St3cmp2vR {
        St3cmp2vR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - SHRTIMER_ST3CMP3V update by DMA mode"]
    #[inline(always)]
    pub fn st3cmp3v(&self) -> St3cmp3vR {
        St3cmp3vR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - SHRTIMER_ST3DTCTL update by DMA mode"]
    #[inline(always)]
    pub fn st3dtctl(&self) -> St3dtctlR {
        St3dtctlR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - SHRTIMER_ST3CH0SET update by DMA mode"]
    #[inline(always)]
    pub fn st3ch0set(&self) -> St3ch0setR {
        St3ch0setR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - SHRTIMER_ST3CH0RST update by DMA mode"]
    #[inline(always)]
    pub fn st3ch0rst(&self) -> St3ch0rstR {
        St3ch0rstR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - SHRTIMER_ST3CH1SET update by DMA mode"]
    #[inline(always)]
    pub fn st3ch1set(&self) -> St3ch1setR {
        St3ch1setR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - SHRTIMER_ST3CH1RST update by DMA mode"]
    #[inline(always)]
    pub fn st3ch1rst(&self) -> St3ch1rstR {
        St3ch1rstR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - SHRTIMER_ST3EXEVFCFG0update by DMA mode"]
    #[inline(always)]
    pub fn st3exevfcfg0(&self) -> St3exevfcfg0R {
        St3exevfcfg0R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - SHRTIMER_ST3EXEVFCFG1update by DMA mode"]
    #[inline(always)]
    pub fn st3exevfcfg1(&self) -> St3exevfcfg1R {
        St3exevfcfg1R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - SHRTIMER_ST3CNTRST update by DMA mode"]
    #[inline(always)]
    pub fn st3cntrst(&self) -> St3cntrstR {
        St3cntrstR::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - SHRTIMER_ST3CSCTL update by DMA mode"]
    #[inline(always)]
    pub fn st3csctl(&self) -> St3csctlR {
        St3csctlR::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - SHRTIMER_ST3CHOCTL update by DMA mode"]
    #[inline(always)]
    pub fn st3choctl(&self) -> St3choctlR {
        St3choctlR::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - SHRTIMER_ST3FLTCTL update by DMA mode"]
    #[inline(always)]
    pub fn st3fltctl(&self) -> St3fltctlR {
        St3fltctlR::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 31 - SHRTIMER_ST3ACTL update by DMA mode"]
    #[inline(always)]
    pub fn st3actl(&self) -> St3actlR {
        St3actlR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - SHRTIMER_ST3CTL0 update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st3ctl0(&mut self) -> St3ctl0W<Dmaupst3rSpec> {
        St3ctl0W::new(self, 0)
    }
    #[doc = "Bit 1 - SHRTIMER_ST3INTC update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st3intc(&mut self) -> St3intcW<Dmaupst3rSpec> {
        St3intcW::new(self, 1)
    }
    #[doc = "Bit 2 - SHRTIMER_ST3DMAINTEN update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st3dmainten(&mut self) -> St3dmaintenW<Dmaupst3rSpec> {
        St3dmaintenW::new(self, 2)
    }
    #[doc = "Bit 3 - SHRTIMER_ST3CNT update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st3cnt(&mut self) -> St3cntW<Dmaupst3rSpec> {
        St3cntW::new(self, 3)
    }
    #[doc = "Bit 4 - SHRTIMER_ST3CAR update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st3car(&mut self) -> St3carW<Dmaupst3rSpec> {
        St3carW::new(self, 4)
    }
    #[doc = "Bit 5 - SHRTIMER_ST3CREP update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st3crep(&mut self) -> St3crepW<Dmaupst3rSpec> {
        St3crepW::new(self, 5)
    }
    #[doc = "Bit 6 - SHRTIMER_ST3CMP0V update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st3cmp0v(&mut self) -> St3cmp0vW<Dmaupst3rSpec> {
        St3cmp0vW::new(self, 6)
    }
    #[doc = "Bit 7 - SHRTIMER_ST3CMP1V update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st3cmp1v(&mut self) -> St3cmp1vW<Dmaupst3rSpec> {
        St3cmp1vW::new(self, 7)
    }
    #[doc = "Bit 8 - SHRTIMER_ST3CMP2V update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st3cmp2v(&mut self) -> St3cmp2vW<Dmaupst3rSpec> {
        St3cmp2vW::new(self, 8)
    }
    #[doc = "Bit 9 - SHRTIMER_ST3CMP3V update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st3cmp3v(&mut self) -> St3cmp3vW<Dmaupst3rSpec> {
        St3cmp3vW::new(self, 9)
    }
    #[doc = "Bit 10 - SHRTIMER_ST3DTCTL update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st3dtctl(&mut self) -> St3dtctlW<Dmaupst3rSpec> {
        St3dtctlW::new(self, 10)
    }
    #[doc = "Bit 11 - SHRTIMER_ST3CH0SET update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st3ch0set(&mut self) -> St3ch0setW<Dmaupst3rSpec> {
        St3ch0setW::new(self, 11)
    }
    #[doc = "Bit 12 - SHRTIMER_ST3CH0RST update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st3ch0rst(&mut self) -> St3ch0rstW<Dmaupst3rSpec> {
        St3ch0rstW::new(self, 12)
    }
    #[doc = "Bit 13 - SHRTIMER_ST3CH1SET update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st3ch1set(&mut self) -> St3ch1setW<Dmaupst3rSpec> {
        St3ch1setW::new(self, 13)
    }
    #[doc = "Bit 14 - SHRTIMER_ST3CH1RST update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st3ch1rst(&mut self) -> St3ch1rstW<Dmaupst3rSpec> {
        St3ch1rstW::new(self, 14)
    }
    #[doc = "Bit 15 - SHRTIMER_ST3EXEVFCFG0update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st3exevfcfg0(&mut self) -> St3exevfcfg0W<Dmaupst3rSpec> {
        St3exevfcfg0W::new(self, 15)
    }
    #[doc = "Bit 16 - SHRTIMER_ST3EXEVFCFG1update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st3exevfcfg1(&mut self) -> St3exevfcfg1W<Dmaupst3rSpec> {
        St3exevfcfg1W::new(self, 16)
    }
    #[doc = "Bit 17 - SHRTIMER_ST3CNTRST update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st3cntrst(&mut self) -> St3cntrstW<Dmaupst3rSpec> {
        St3cntrstW::new(self, 17)
    }
    #[doc = "Bit 18 - SHRTIMER_ST3CSCTL update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st3csctl(&mut self) -> St3csctlW<Dmaupst3rSpec> {
        St3csctlW::new(self, 18)
    }
    #[doc = "Bit 19 - SHRTIMER_ST3CHOCTL update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st3choctl(&mut self) -> St3choctlW<Dmaupst3rSpec> {
        St3choctlW::new(self, 19)
    }
    #[doc = "Bit 20 - SHRTIMER_ST3FLTCTL update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st3fltctl(&mut self) -> St3fltctlW<Dmaupst3rSpec> {
        St3fltctlW::new(self, 20)
    }
    #[doc = "Bit 31 - SHRTIMER_ST3ACTL update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn st3actl(&mut self) -> St3actlW<Dmaupst3rSpec> {
        St3actlW::new(self, 31)
    }
}
#[doc = "SHRTIMER DMA update Slave_TIMER3 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dmaupst3r::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dmaupst3r::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Dmaupst3rSpec;
impl crate::RegisterSpec for Dmaupst3rSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dmaupst3r::R`](R) reader structure"]
impl crate::Readable for Dmaupst3rSpec {}
#[doc = "`write(|w| ..)` method takes [`dmaupst3r::W`](W) writer structure"]
impl crate::Writable for Dmaupst3rSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DMAUPST3R to value 0"]
impl crate::Resettable for Dmaupst3rSpec {
    const RESET_VALUE: u32 = 0;
}
