#[doc = "Register `CHOUTEN` reader"]
pub type R = crate::R<ChoutenSpec>;
#[doc = "Register `CHOUTEN` writer"]
pub type W = crate::W<ChoutenSpec>;
#[doc = "Field `ST0CH0EN` reader - Slave_TIMER0 channel 0 output (ST0CH0_O) enable"]
pub type St0ch0enR = crate::BitReader;
#[doc = "Field `ST0CH0EN` writer - Slave_TIMER0 channel 0 output (ST0CH0_O) enable"]
pub type St0ch0enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0CH1EN` reader - Slave_TIMER0 channel 1 output (ST0CH1_O) enable"]
pub type St0ch1enR = crate::BitReader;
#[doc = "Field `ST0CH1EN` writer - Slave_TIMER0 channel 1 output (ST0CH1_O) enable"]
pub type St0ch1enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1CH0EN` reader - Slave_TIMER1 channel 0 output (ST1CH0_O) enable"]
pub type St1ch0enR = crate::BitReader;
#[doc = "Field `ST1CH0EN` writer - Slave_TIMER1 channel 0 output (ST1CH0_O) enable"]
pub type St1ch0enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1CH1EN` reader - Slave_TIMER1 channel 1 output (ST1CH1_O) enable"]
pub type St1ch1enR = crate::BitReader;
#[doc = "Field `ST1CH1EN` writer - Slave_TIMER1 channel 1 output (ST1CH1_O) enable"]
pub type St1ch1enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2CH0EN` reader - Slave_TIMER2 channel 0 output (ST2CH0_O) enable"]
pub type St2ch0enR = crate::BitReader;
#[doc = "Field `ST2CH0EN` writer - Slave_TIMER2 channel 0 output (ST2CH0_O) enable"]
pub type St2ch0enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2CH1EN` reader - Slave_TIMER2 channel 1 output (ST2CH1_O) enable"]
pub type St2ch1enR = crate::BitReader;
#[doc = "Field `ST2CH1EN` writer - Slave_TIMER2 channel 1 output (ST2CH1_O) enable"]
pub type St2ch1enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3CH0EN` reader - Slave_TIMER3 channel 0 output (ST3CH0_O) enable"]
pub type St3ch0enR = crate::BitReader;
#[doc = "Field `ST3CH0EN` writer - Slave_TIMER3 channel 0 output (ST3CH0_O) enable"]
pub type St3ch0enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3CH1EN` reader - Slave_TIMER3 channel 1 output (ST3CH1_O) enable"]
pub type St3ch1enR = crate::BitReader;
#[doc = "Field `ST3CH1EN` writer - Slave_TIMER3 channel 1 output (ST3CH1_O) enable"]
pub type St3ch1enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4CH0EN` reader - Slave_TIMER4 channel 0 output (ST4CH0_O) enable"]
pub type St4ch0enR = crate::BitReader;
#[doc = "Field `ST4CH0EN` writer - Slave_TIMER4 channel 0 output (ST4CH0_O) enable"]
pub type St4ch0enW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4CH1EN` reader - Slave_TIMER4 channel 1 output (ST4CH1_O) enable"]
pub type St4ch1enR = crate::BitReader;
#[doc = "Field `ST4CH1EN` writer - Slave_TIMER4 channel 1 output (ST4CH1_O) enable"]
pub type St4ch1enW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Slave_TIMER0 channel 0 output (ST0CH0_O) enable"]
    #[inline(always)]
    pub fn st0ch0en(&self) -> St0ch0enR {
        St0ch0enR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Slave_TIMER0 channel 1 output (ST0CH1_O) enable"]
    #[inline(always)]
    pub fn st0ch1en(&self) -> St0ch1enR {
        St0ch1enR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Slave_TIMER1 channel 0 output (ST1CH0_O) enable"]
    #[inline(always)]
    pub fn st1ch0en(&self) -> St1ch0enR {
        St1ch0enR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Slave_TIMER1 channel 1 output (ST1CH1_O) enable"]
    #[inline(always)]
    pub fn st1ch1en(&self) -> St1ch1enR {
        St1ch1enR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Slave_TIMER2 channel 0 output (ST2CH0_O) enable"]
    #[inline(always)]
    pub fn st2ch0en(&self) -> St2ch0enR {
        St2ch0enR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Slave_TIMER2 channel 1 output (ST2CH1_O) enable"]
    #[inline(always)]
    pub fn st2ch1en(&self) -> St2ch1enR {
        St2ch1enR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Slave_TIMER3 channel 0 output (ST3CH0_O) enable"]
    #[inline(always)]
    pub fn st3ch0en(&self) -> St3ch0enR {
        St3ch0enR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Slave_TIMER3 channel 1 output (ST3CH1_O) enable"]
    #[inline(always)]
    pub fn st3ch1en(&self) -> St3ch1enR {
        St3ch1enR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Slave_TIMER4 channel 0 output (ST4CH0_O) enable"]
    #[inline(always)]
    pub fn st4ch0en(&self) -> St4ch0enR {
        St4ch0enR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Slave_TIMER4 channel 1 output (ST4CH1_O) enable"]
    #[inline(always)]
    pub fn st4ch1en(&self) -> St4ch1enR {
        St4ch1enR::new(((self.bits >> 9) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Slave_TIMER0 channel 0 output (ST0CH0_O) enable"]
    #[inline(always)]
    #[must_use]
    pub fn st0ch0en(&mut self) -> St0ch0enW<ChoutenSpec> {
        St0ch0enW::new(self, 0)
    }
    #[doc = "Bit 1 - Slave_TIMER0 channel 1 output (ST0CH1_O) enable"]
    #[inline(always)]
    #[must_use]
    pub fn st0ch1en(&mut self) -> St0ch1enW<ChoutenSpec> {
        St0ch1enW::new(self, 1)
    }
    #[doc = "Bit 2 - Slave_TIMER1 channel 0 output (ST1CH0_O) enable"]
    #[inline(always)]
    #[must_use]
    pub fn st1ch0en(&mut self) -> St1ch0enW<ChoutenSpec> {
        St1ch0enW::new(self, 2)
    }
    #[doc = "Bit 3 - Slave_TIMER1 channel 1 output (ST1CH1_O) enable"]
    #[inline(always)]
    #[must_use]
    pub fn st1ch1en(&mut self) -> St1ch1enW<ChoutenSpec> {
        St1ch1enW::new(self, 3)
    }
    #[doc = "Bit 4 - Slave_TIMER2 channel 0 output (ST2CH0_O) enable"]
    #[inline(always)]
    #[must_use]
    pub fn st2ch0en(&mut self) -> St2ch0enW<ChoutenSpec> {
        St2ch0enW::new(self, 4)
    }
    #[doc = "Bit 5 - Slave_TIMER2 channel 1 output (ST2CH1_O) enable"]
    #[inline(always)]
    #[must_use]
    pub fn st2ch1en(&mut self) -> St2ch1enW<ChoutenSpec> {
        St2ch1enW::new(self, 5)
    }
    #[doc = "Bit 6 - Slave_TIMER3 channel 0 output (ST3CH0_O) enable"]
    #[inline(always)]
    #[must_use]
    pub fn st3ch0en(&mut self) -> St3ch0enW<ChoutenSpec> {
        St3ch0enW::new(self, 6)
    }
    #[doc = "Bit 7 - Slave_TIMER3 channel 1 output (ST3CH1_O) enable"]
    #[inline(always)]
    #[must_use]
    pub fn st3ch1en(&mut self) -> St3ch1enW<ChoutenSpec> {
        St3ch1enW::new(self, 7)
    }
    #[doc = "Bit 8 - Slave_TIMER4 channel 0 output (ST4CH0_O) enable"]
    #[inline(always)]
    #[must_use]
    pub fn st4ch0en(&mut self) -> St4ch0enW<ChoutenSpec> {
        St4ch0enW::new(self, 8)
    }
    #[doc = "Bit 9 - Slave_TIMER4 channel 1 output (ST4CH1_O) enable"]
    #[inline(always)]
    #[must_use]
    pub fn st4ch1en(&mut self) -> St4ch1enW<ChoutenSpec> {
        St4ch1enW::new(self, 9)
    }
}
#[doc = "SHRTIMER channel output enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`chouten::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`chouten::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ChoutenSpec;
impl crate::RegisterSpec for ChoutenSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`chouten::R`](R) reader structure"]
impl crate::Readable for ChoutenSpec {}
#[doc = "`write(|w| ..)` method takes [`chouten::W`](W) writer structure"]
impl crate::Writable for ChoutenSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CHOUTEN to value 0"]
impl crate::Resettable for ChoutenSpec {
    const RESET_VALUE: u32 = 0;
}
