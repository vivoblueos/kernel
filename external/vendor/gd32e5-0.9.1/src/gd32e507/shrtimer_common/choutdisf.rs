#[doc = "Register `CHOUTDISF` reader"]
pub type R = crate::R<ChoutdisfSpec>;
#[doc = "Field `ST0CH0DISF` reader - Slave_TIMER0 channel 0 output (ST0CH0_O) disable flag"]
pub type St0ch0disfR = crate::BitReader;
#[doc = "Field `ST0CH1DISF` reader - Slave_TIMER0 channel 1 output (ST0CH1_O) disable flag"]
pub type St0ch1disfR = crate::BitReader;
#[doc = "Field `ST1CH0DISF` reader - Slave_TIMER1 channel 0 output (ST1CH0_O) disable flag"]
pub type St1ch0disfR = crate::BitReader;
#[doc = "Field `ST1CH1DISF` reader - Slave_TIMER1 channel 1 output (ST1CH1_O) disable flag"]
pub type St1ch1disfR = crate::BitReader;
#[doc = "Field `ST2CH0DISF` reader - Slave_TIMER2 channel 0 output (ST2CH0_O) disable flag"]
pub type St2ch0disfR = crate::BitReader;
#[doc = "Field `ST2CH1DISF` reader - Slave_TIMER2 channel 1 output (ST2CH1_O) disable flag"]
pub type St2ch1disfR = crate::BitReader;
#[doc = "Field `ST3CH0DISF` reader - Slave_TIMER3 channel 0 output (ST3CH0_O) disable flag"]
pub type St3ch0disfR = crate::BitReader;
#[doc = "Field `ST3CH1DISF` reader - Slave_TIMER3 channel 1 output (ST3CH1_O) disable flag"]
pub type St3ch1disfR = crate::BitReader;
#[doc = "Field `ST4CH0DISF` reader - Slave_TIMER4 channel 0 output (ST4CH0_O) disable flag"]
pub type St4ch0disfR = crate::BitReader;
#[doc = "Field `ST4CH1DISF` reader - Slave_TIMER4 channel 1 output (ST4CH1_O) disable flag"]
pub type St4ch1disfR = crate::BitReader;
impl R {
    #[doc = "Bit 0 - Slave_TIMER0 channel 0 output (ST0CH0_O) disable flag"]
    #[inline(always)]
    pub fn st0ch0disf(&self) -> St0ch0disfR {
        St0ch0disfR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Slave_TIMER0 channel 1 output (ST0CH1_O) disable flag"]
    #[inline(always)]
    pub fn st0ch1disf(&self) -> St0ch1disfR {
        St0ch1disfR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Slave_TIMER1 channel 0 output (ST1CH0_O) disable flag"]
    #[inline(always)]
    pub fn st1ch0disf(&self) -> St1ch0disfR {
        St1ch0disfR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Slave_TIMER1 channel 1 output (ST1CH1_O) disable flag"]
    #[inline(always)]
    pub fn st1ch1disf(&self) -> St1ch1disfR {
        St1ch1disfR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Slave_TIMER2 channel 0 output (ST2CH0_O) disable flag"]
    #[inline(always)]
    pub fn st2ch0disf(&self) -> St2ch0disfR {
        St2ch0disfR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Slave_TIMER2 channel 1 output (ST2CH1_O) disable flag"]
    #[inline(always)]
    pub fn st2ch1disf(&self) -> St2ch1disfR {
        St2ch1disfR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Slave_TIMER3 channel 0 output (ST3CH0_O) disable flag"]
    #[inline(always)]
    pub fn st3ch0disf(&self) -> St3ch0disfR {
        St3ch0disfR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Slave_TIMER3 channel 1 output (ST3CH1_O) disable flag"]
    #[inline(always)]
    pub fn st3ch1disf(&self) -> St3ch1disfR {
        St3ch1disfR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Slave_TIMER4 channel 0 output (ST4CH0_O) disable flag"]
    #[inline(always)]
    pub fn st4ch0disf(&self) -> St4ch0disfR {
        St4ch0disfR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Slave_TIMER4 channel 1 output (ST4CH1_O) disable flag"]
    #[inline(always)]
    pub fn st4ch1disf(&self) -> St4ch1disfR {
        St4ch1disfR::new(((self.bits >> 9) & 1) != 0)
    }
}
#[doc = "SHRTIMER channel output disable flag register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`choutdisf::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct ChoutdisfSpec;
impl crate::RegisterSpec for ChoutdisfSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`choutdisf::R`](R) reader structure"]
impl crate::Readable for ChoutdisfSpec {}
#[doc = "`reset()` method sets CHOUTDISF to value 0"]
impl crate::Resettable for ChoutdisfSpec {
    const RESET_VALUE: u32 = 0;
}
