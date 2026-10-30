#[doc = "Register `CTL1` reader"]
pub type R = crate::R<Ctl1Spec>;
#[doc = "Register `CTL1` writer"]
pub type W = crate::W<Ctl1Spec>;
#[doc = "Field `FIFOEN0` reader - DAC_OUT0 data FIFO enable"]
pub type Fifoen0R = crate::BitReader;
#[doc = "Field `FIFOEN0` writer - DAC_OUT0 data FIFO enable"]
pub type Fifoen0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FIFOOVRIE0` reader - DAC_OUT0 FIFO overflow interrupt enable"]
pub type Fifoovrie0R = crate::BitReader;
#[doc = "Field `FIFOOVRIE0` writer - DAC_OUT0 FIFO overflow interrupt enable"]
pub type Fifoovrie0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FIFOUDRIE0` reader - DAC_OUT0 FIFO underflow interrupt enable"]
pub type Fifoudrie0R = crate::BitReader;
#[doc = "Field `FIFOUDRIE0` writer - DAC_OUT0 FIFO underflow interrupt enable"]
pub type Fifoudrie0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FIFOEN1` reader - DAC_OUT1 data FIFO enable"]
pub type Fifoen1R = crate::BitReader;
#[doc = "Field `FIFOEN1` writer - DAC_OUT1 data FIFO enable"]
pub type Fifoen1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FIFOOVRIE1` reader - DAC_OUT1 FIFO overflow interrupt enable"]
pub type Fifoovrie1R = crate::BitReader;
#[doc = "Field `FIFOOVRIE1` writer - DAC_OUT1 FIFO overflow interrupt enable"]
pub type Fifoovrie1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FIFOUDRIE1` reader - DAC_OUT1 FIFO underflow interrupt enable"]
pub type Fifoudrie1R = crate::BitReader;
#[doc = "Field `FIFOUDRIE1` writer - DAC_OUT1 FIFO underflow interrupt enable"]
pub type Fifoudrie1W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - DAC_OUT0 data FIFO enable"]
    #[inline(always)]
    pub fn fifoen0(&self) -> Fifoen0R {
        Fifoen0R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - DAC_OUT0 FIFO overflow interrupt enable"]
    #[inline(always)]
    pub fn fifoovrie0(&self) -> Fifoovrie0R {
        Fifoovrie0R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - DAC_OUT0 FIFO underflow interrupt enable"]
    #[inline(always)]
    pub fn fifoudrie0(&self) -> Fifoudrie0R {
        Fifoudrie0R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 16 - DAC_OUT1 data FIFO enable"]
    #[inline(always)]
    pub fn fifoen1(&self) -> Fifoen1R {
        Fifoen1R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - DAC_OUT1 FIFO overflow interrupt enable"]
    #[inline(always)]
    pub fn fifoovrie1(&self) -> Fifoovrie1R {
        Fifoovrie1R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - DAC_OUT1 FIFO underflow interrupt enable"]
    #[inline(always)]
    pub fn fifoudrie1(&self) -> Fifoudrie1R {
        Fifoudrie1R::new(((self.bits >> 18) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - DAC_OUT0 data FIFO enable"]
    #[inline(always)]
    #[must_use]
    pub fn fifoen0(&mut self) -> Fifoen0W<Ctl1Spec> {
        Fifoen0W::new(self, 0)
    }
    #[doc = "Bit 1 - DAC_OUT0 FIFO overflow interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn fifoovrie0(&mut self) -> Fifoovrie0W<Ctl1Spec> {
        Fifoovrie0W::new(self, 1)
    }
    #[doc = "Bit 2 - DAC_OUT0 FIFO underflow interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn fifoudrie0(&mut self) -> Fifoudrie0W<Ctl1Spec> {
        Fifoudrie0W::new(self, 2)
    }
    #[doc = "Bit 16 - DAC_OUT1 data FIFO enable"]
    #[inline(always)]
    #[must_use]
    pub fn fifoen1(&mut self) -> Fifoen1W<Ctl1Spec> {
        Fifoen1W::new(self, 16)
    }
    #[doc = "Bit 17 - DAC_OUT1 FIFO overflow interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn fifoovrie1(&mut self) -> Fifoovrie1W<Ctl1Spec> {
        Fifoovrie1W::new(self, 17)
    }
    #[doc = "Bit 18 - DAC_OUT1 FIFO underflow interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn fifoudrie1(&mut self) -> Fifoudrie1W<Ctl1Spec> {
        Fifoudrie1W::new(self, 18)
    }
}
#[doc = "DAC Control Register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl1::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl1::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ctl1Spec;
impl crate::RegisterSpec for Ctl1Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ctl1::R`](R) reader structure"]
impl crate::Readable for Ctl1Spec {}
#[doc = "`write(|w| ..)` method takes [`ctl1::W`](W) writer structure"]
impl crate::Writable for Ctl1Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CTL1 to value 0"]
impl crate::Resettable for Ctl1Spec {
    const RESET_VALUE: u32 = 0;
}
