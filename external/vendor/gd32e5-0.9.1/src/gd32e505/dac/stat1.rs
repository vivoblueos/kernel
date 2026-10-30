#[doc = "Register `STAT1` reader"]
pub type R = crate::R<Stat1Spec>;
#[doc = "Register `STAT1` writer"]
pub type W = crate::W<Stat1Spec>;
#[doc = "Field `FF0` reader - DAC_OUT0 FIFO full flag"]
pub type Ff0R = crate::BitReader;
#[doc = "Field `FE0` reader - DAC_OUT0 FIFO empty flag"]
pub type Fe0R = crate::BitReader;
#[doc = "Field `FIFOOVR0` reader - DAC_OUT0 FIFO overflow flag"]
pub type Fifoovr0R = crate::BitReader;
#[doc = "Field `FIFOOVR0` writer - DAC_OUT0 FIFO overflow flag"]
pub type Fifoovr0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FIFOUDR0` reader - DAC_OUT0 FIFO underflow flag"]
pub type Fifoudr0R = crate::BitReader;
#[doc = "Field `FIFOUDR0` writer - DAC_OUT0 FIFO underflow flag"]
pub type Fifoudr0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FIFONUM0` reader - Number of data in the DAC_OUT0 FIFO"]
pub type Fifonum0R = crate::FieldReader;
#[doc = "Field `FF1` reader - DAC_OUT1 FIFO full flag"]
pub type Ff1R = crate::BitReader;
#[doc = "Field `FE1` reader - DAC_OUT1 FIFO empty flag"]
pub type Fe1R = crate::BitReader;
#[doc = "Field `FIFOOVR1` reader - DAC_OUT1 FIFO overflow flag"]
pub type Fifoovr1R = crate::BitReader;
#[doc = "Field `FIFOOVR1` writer - DAC_OUT1 FIFO overflow flag"]
pub type Fifoovr1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FIFOUDR1` reader - DAC_OUT1 FIFO underflow flag"]
pub type Fifoudr1R = crate::BitReader;
#[doc = "Field `FIFOUDR1` writer - DAC_OUT1 FIFO underflow flag"]
pub type Fifoudr1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FIFONUM1` reader - Number of data in the DAC_OUT1 FIFO"]
pub type Fifonum1R = crate::FieldReader;
impl R {
    #[doc = "Bit 0 - DAC_OUT0 FIFO full flag"]
    #[inline(always)]
    pub fn ff0(&self) -> Ff0R {
        Ff0R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - DAC_OUT0 FIFO empty flag"]
    #[inline(always)]
    pub fn fe0(&self) -> Fe0R {
        Fe0R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - DAC_OUT0 FIFO overflow flag"]
    #[inline(always)]
    pub fn fifoovr0(&self) -> Fifoovr0R {
        Fifoovr0R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - DAC_OUT0 FIFO underflow flag"]
    #[inline(always)]
    pub fn fifoudr0(&self) -> Fifoudr0R {
        Fifoudr0R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bits 4:6 - Number of data in the DAC_OUT0 FIFO"]
    #[inline(always)]
    pub fn fifonum0(&self) -> Fifonum0R {
        Fifonum0R::new(((self.bits >> 4) & 7) as u8)
    }
    #[doc = "Bit 16 - DAC_OUT1 FIFO full flag"]
    #[inline(always)]
    pub fn ff1(&self) -> Ff1R {
        Ff1R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - DAC_OUT1 FIFO empty flag"]
    #[inline(always)]
    pub fn fe1(&self) -> Fe1R {
        Fe1R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - DAC_OUT1 FIFO overflow flag"]
    #[inline(always)]
    pub fn fifoovr1(&self) -> Fifoovr1R {
        Fifoovr1R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - DAC_OUT1 FIFO underflow flag"]
    #[inline(always)]
    pub fn fifoudr1(&self) -> Fifoudr1R {
        Fifoudr1R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bits 20:22 - Number of data in the DAC_OUT1 FIFO"]
    #[inline(always)]
    pub fn fifonum1(&self) -> Fifonum1R {
        Fifonum1R::new(((self.bits >> 20) & 7) as u8)
    }
}
impl W {
    #[doc = "Bit 2 - DAC_OUT0 FIFO overflow flag"]
    #[inline(always)]
    #[must_use]
    pub fn fifoovr0(&mut self) -> Fifoovr0W<Stat1Spec> {
        Fifoovr0W::new(self, 2)
    }
    #[doc = "Bit 3 - DAC_OUT0 FIFO underflow flag"]
    #[inline(always)]
    #[must_use]
    pub fn fifoudr0(&mut self) -> Fifoudr0W<Stat1Spec> {
        Fifoudr0W::new(self, 3)
    }
    #[doc = "Bit 18 - DAC_OUT1 FIFO overflow flag"]
    #[inline(always)]
    #[must_use]
    pub fn fifoovr1(&mut self) -> Fifoovr1W<Stat1Spec> {
        Fifoovr1W::new(self, 18)
    }
    #[doc = "Bit 19 - DAC_OUT1 FIFO underflow flag"]
    #[inline(always)]
    #[must_use]
    pub fn fifoudr1(&mut self) -> Fifoudr1W<Stat1Spec> {
        Fifoudr1W::new(self, 19)
    }
}
#[doc = "DAC Status register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`stat1::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`stat1::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Stat1Spec;
impl crate::RegisterSpec for Stat1Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`stat1::R`](R) reader structure"]
impl crate::Readable for Stat1Spec {}
#[doc = "`write(|w| ..)` method takes [`stat1::W`](W) writer structure"]
impl crate::Writable for Stat1Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets STAT1 to value 0x02"]
impl crate::Resettable for Stat1Spec {
    const RESET_VALUE: u32 = 0x02;
}
