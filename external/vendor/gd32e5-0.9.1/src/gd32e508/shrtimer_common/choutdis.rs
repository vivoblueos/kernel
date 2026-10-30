#[doc = "Register `CHOUTDIS` writer"]
pub type W = crate::W<ChoutdisSpec>;
#[doc = "Field `ST0CH0DIS` writer - Slave_TIMER0 channel 0 output (ST0CH0_O) disable"]
pub type St0ch0disW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0CH1DIS` writer - Slave_TIMER0 channel 1 output (ST4CH0_O) disable"]
pub type St0ch1disW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1CH0DIS` writer - Slave_TIMER1 channel 0 output (ST1CH0_O) disable"]
pub type St1ch0disW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1CH1DIS` writer - Slave_TIMER1 channel 1 output (ST1CH1_O) disable"]
pub type St1ch1disW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2CH0DIS` writer - Slave_TIMER2 channel 0 output (ST2CH0_O) disable"]
pub type St2ch0disW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2CH1DIS` writer - Slave_TIMER2 channel 1 output (ST2CH1_O) disable"]
pub type St2ch1disW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3CH0DIS` writer - Slave_TIMER3 channel 0 output (ST3CH0_O) disable"]
pub type St3ch0disW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3CH1DIS` writer - Slave_TIMER3 channel 1 output (ST3CH1_O) disable"]
pub type St3ch1disW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4CH0DIS` writer - Slave_TIMER4 channel 0 output (ST4CH0_O) disable"]
pub type St4ch0disW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4CH1DIS` writer - Slave_TIMER4 channel 1 output (ST4CH1_O) disable"]
pub type St4ch1disW<'a, REG> = crate::BitWriter<'a, REG>;
impl W {
    #[doc = "Bit 0 - Slave_TIMER0 channel 0 output (ST0CH0_O) disable"]
    #[inline(always)]
    #[must_use]
    pub fn st0ch0dis(&mut self) -> St0ch0disW<ChoutdisSpec> {
        St0ch0disW::new(self, 0)
    }
    #[doc = "Bit 1 - Slave_TIMER0 channel 1 output (ST4CH0_O) disable"]
    #[inline(always)]
    #[must_use]
    pub fn st0ch1dis(&mut self) -> St0ch1disW<ChoutdisSpec> {
        St0ch1disW::new(self, 1)
    }
    #[doc = "Bit 2 - Slave_TIMER1 channel 0 output (ST1CH0_O) disable"]
    #[inline(always)]
    #[must_use]
    pub fn st1ch0dis(&mut self) -> St1ch0disW<ChoutdisSpec> {
        St1ch0disW::new(self, 2)
    }
    #[doc = "Bit 3 - Slave_TIMER1 channel 1 output (ST1CH1_O) disable"]
    #[inline(always)]
    #[must_use]
    pub fn st1ch1dis(&mut self) -> St1ch1disW<ChoutdisSpec> {
        St1ch1disW::new(self, 3)
    }
    #[doc = "Bit 4 - Slave_TIMER2 channel 0 output (ST2CH0_O) disable"]
    #[inline(always)]
    #[must_use]
    pub fn st2ch0dis(&mut self) -> St2ch0disW<ChoutdisSpec> {
        St2ch0disW::new(self, 4)
    }
    #[doc = "Bit 5 - Slave_TIMER2 channel 1 output (ST2CH1_O) disable"]
    #[inline(always)]
    #[must_use]
    pub fn st2ch1dis(&mut self) -> St2ch1disW<ChoutdisSpec> {
        St2ch1disW::new(self, 5)
    }
    #[doc = "Bit 6 - Slave_TIMER3 channel 0 output (ST3CH0_O) disable"]
    #[inline(always)]
    #[must_use]
    pub fn st3ch0dis(&mut self) -> St3ch0disW<ChoutdisSpec> {
        St3ch0disW::new(self, 6)
    }
    #[doc = "Bit 7 - Slave_TIMER3 channel 1 output (ST3CH1_O) disable"]
    #[inline(always)]
    #[must_use]
    pub fn st3ch1dis(&mut self) -> St3ch1disW<ChoutdisSpec> {
        St3ch1disW::new(self, 7)
    }
    #[doc = "Bit 8 - Slave_TIMER4 channel 0 output (ST4CH0_O) disable"]
    #[inline(always)]
    #[must_use]
    pub fn st4ch0dis(&mut self) -> St4ch0disW<ChoutdisSpec> {
        St4ch0disW::new(self, 8)
    }
    #[doc = "Bit 9 - Slave_TIMER4 channel 1 output (ST4CH1_O) disable"]
    #[inline(always)]
    #[must_use]
    pub fn st4ch1dis(&mut self) -> St4ch1disW<ChoutdisSpec> {
        St4ch1disW::new(self, 9)
    }
}
#[doc = "SHRTIMER channel output disable register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`choutdis::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ChoutdisSpec;
impl crate::RegisterSpec for ChoutdisSpec {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`choutdis::W`](W) writer structure"]
impl crate::Writable for ChoutdisSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CHOUTDIS to value 0"]
impl crate::Resettable for ChoutdisSpec {
    const RESET_VALUE: u32 = 0;
}
