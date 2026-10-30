#[doc = "Register `CTL0` reader"]
pub type R = crate::R<Ctl0Spec>;
#[doc = "Register `CTL0` writer"]
pub type W = crate::W<Ctl0Spec>;
#[doc = "Field `MTUPDIS` reader - Master_TIMER update disable"]
pub type MtupdisR = crate::BitReader;
#[doc = "Field `MTUPDIS` writer - Master_TIMER update disable"]
pub type MtupdisW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0UPDIS` reader - Slave_TIMER0 update disable"]
pub type St0updisR = crate::BitReader;
#[doc = "Field `ST0UPDIS` writer - Slave_TIMER0 update disable"]
pub type St0updisW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2UPDIS` reader - Slave_TIMER2 update disable"]
pub type St2updisR = crate::BitReader;
#[doc = "Field `ST2UPDIS` writer - Slave_TIMER2 update disable"]
pub type St2updisW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3UPDIS` reader - Slave_TIMER3 update disable"]
pub type St3updisR = crate::BitReader;
#[doc = "Field `ST3UPDIS` writer - Slave_TIMER3 update disable"]
pub type St3updisW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4UPDIS` reader - Slave_TIMER4 update disable"]
pub type St4updisR = crate::BitReader;
#[doc = "Field `ST4UPDIS` writer - Slave_TIMER4 update disable"]
pub type St4updisW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ADTG0USRC` reader - SHRTIMER_ADCTRIG0 update source"]
pub type Adtg0usrcR = crate::FieldReader;
#[doc = "Field `ADTG0USRC` writer - SHRTIMER_ADCTRIG0 update source"]
pub type Adtg0usrcW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `ADTG1USRC` reader - SHRTIMER_ADCTRIG1 update source"]
pub type Adtg1usrcR = crate::FieldReader;
#[doc = "Field `ADTG1USRC` writer - SHRTIMER_ADCTRIG1 update source"]
pub type Adtg1usrcW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `ADTG2USRC` reader - SHRTIMER_ADCTRIG2 update source"]
pub type Adtg2usrcR = crate::FieldReader;
#[doc = "Field `ADTG2USRC` writer - SHRTIMER_ADCTRIG2 update source"]
pub type Adtg2usrcW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `ADTG3USRC` reader - SHRTIMER_ADCTRIG3 update source"]
pub type Adtg3usrcR = crate::FieldReader;
#[doc = "Field `ADTG3USRC` writer - SHRTIMER_ADCTRIG3 update source"]
pub type Adtg3usrcW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
impl R {
    #[doc = "Bit 0 - Master_TIMER update disable"]
    #[inline(always)]
    pub fn mtupdis(&self) -> MtupdisR {
        MtupdisR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Slave_TIMER0 update disable"]
    #[inline(always)]
    pub fn st0updis(&self) -> St0updisR {
        St0updisR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 3 - Slave_TIMER2 update disable"]
    #[inline(always)]
    pub fn st2updis(&self) -> St2updisR {
        St2updisR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Slave_TIMER3 update disable"]
    #[inline(always)]
    pub fn st3updis(&self) -> St3updisR {
        St3updisR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Slave_TIMER4 update disable"]
    #[inline(always)]
    pub fn st4updis(&self) -> St4updisR {
        St4updisR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bits 16:18 - SHRTIMER_ADCTRIG0 update source"]
    #[inline(always)]
    pub fn adtg0usrc(&self) -> Adtg0usrcR {
        Adtg0usrcR::new(((self.bits >> 16) & 7) as u8)
    }
    #[doc = "Bits 19:21 - SHRTIMER_ADCTRIG1 update source"]
    #[inline(always)]
    pub fn adtg1usrc(&self) -> Adtg1usrcR {
        Adtg1usrcR::new(((self.bits >> 19) & 7) as u8)
    }
    #[doc = "Bits 22:24 - SHRTIMER_ADCTRIG2 update source"]
    #[inline(always)]
    pub fn adtg2usrc(&self) -> Adtg2usrcR {
        Adtg2usrcR::new(((self.bits >> 22) & 7) as u8)
    }
    #[doc = "Bits 25:27 - SHRTIMER_ADCTRIG3 update source"]
    #[inline(always)]
    pub fn adtg3usrc(&self) -> Adtg3usrcR {
        Adtg3usrcR::new(((self.bits >> 25) & 7) as u8)
    }
}
impl W {
    #[doc = "Bit 0 - Master_TIMER update disable"]
    #[inline(always)]
    #[must_use]
    pub fn mtupdis(&mut self) -> MtupdisW<Ctl0Spec> {
        MtupdisW::new(self, 0)
    }
    #[doc = "Bit 1 - Slave_TIMER0 update disable"]
    #[inline(always)]
    #[must_use]
    pub fn st0updis(&mut self) -> St0updisW<Ctl0Spec> {
        St0updisW::new(self, 1)
    }
    #[doc = "Bit 3 - Slave_TIMER2 update disable"]
    #[inline(always)]
    #[must_use]
    pub fn st2updis(&mut self) -> St2updisW<Ctl0Spec> {
        St2updisW::new(self, 3)
    }
    #[doc = "Bit 4 - Slave_TIMER3 update disable"]
    #[inline(always)]
    #[must_use]
    pub fn st3updis(&mut self) -> St3updisW<Ctl0Spec> {
        St3updisW::new(self, 4)
    }
    #[doc = "Bit 5 - Slave_TIMER4 update disable"]
    #[inline(always)]
    #[must_use]
    pub fn st4updis(&mut self) -> St4updisW<Ctl0Spec> {
        St4updisW::new(self, 5)
    }
    #[doc = "Bits 16:18 - SHRTIMER_ADCTRIG0 update source"]
    #[inline(always)]
    #[must_use]
    pub fn adtg0usrc(&mut self) -> Adtg0usrcW<Ctl0Spec> {
        Adtg0usrcW::new(self, 16)
    }
    #[doc = "Bits 19:21 - SHRTIMER_ADCTRIG1 update source"]
    #[inline(always)]
    #[must_use]
    pub fn adtg1usrc(&mut self) -> Adtg1usrcW<Ctl0Spec> {
        Adtg1usrcW::new(self, 19)
    }
    #[doc = "Bits 22:24 - SHRTIMER_ADCTRIG2 update source"]
    #[inline(always)]
    #[must_use]
    pub fn adtg2usrc(&mut self) -> Adtg2usrcW<Ctl0Spec> {
        Adtg2usrcW::new(self, 22)
    }
    #[doc = "Bits 25:27 - SHRTIMER_ADCTRIG3 update source"]
    #[inline(always)]
    #[must_use]
    pub fn adtg3usrc(&mut self) -> Adtg3usrcW<Ctl0Spec> {
        Adtg3usrcW::new(self, 25)
    }
}
#[doc = "SHRTIMER control register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl0::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl0::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ctl0Spec;
impl crate::RegisterSpec for Ctl0Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctl0::R`](R) reader structure"]
impl crate::Readable for Ctl0Spec {}
#[doc = "`write(|w| ..)` method takes [`ctl0::W`](W) writer structure"]
impl crate::Writable for Ctl0Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CTL0 to value 0"]
impl crate::Resettable for Ctl0Spec {
    const RESET_VALUE: u32 = 0;
}
