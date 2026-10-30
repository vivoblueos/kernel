#[doc = "Register `RFIFO1` reader"]
pub type R = crate::R<Rfifo1Spec>;
#[doc = "Register `RFIFO1` writer"]
pub type W = crate::W<Rfifo1Spec>;
#[doc = "Field `RFL1` reader - Receive FIFO1 length"]
pub type Rfl1R = crate::FieldReader;
#[doc = "Field `RFF1` reader - Receive FIFO1 full"]
pub type Rff1R = crate::BitReader;
#[doc = "Field `RFF1` writer - Receive FIFO1 full"]
pub type Rff1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RFO1` reader - Receive FIFO1 overfull"]
pub type Rfo1R = crate::BitReader;
#[doc = "Field `RFO1` writer - Receive FIFO1 overfull"]
pub type Rfo1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RFD1` reader - Receive FIFO1 dequeue"]
pub type Rfd1R = crate::BitReader;
#[doc = "Field `RFD1` writer - Receive FIFO1 dequeue"]
pub type Rfd1W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:1 - Receive FIFO1 length"]
    #[inline(always)]
    pub fn rfl1(&self) -> Rfl1R {
        Rfl1R::new((self.bits & 3) as u8)
    }
    #[doc = "Bit 3 - Receive FIFO1 full"]
    #[inline(always)]
    pub fn rff1(&self) -> Rff1R {
        Rff1R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Receive FIFO1 overfull"]
    #[inline(always)]
    pub fn rfo1(&self) -> Rfo1R {
        Rfo1R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Receive FIFO1 dequeue"]
    #[inline(always)]
    pub fn rfd1(&self) -> Rfd1R {
        Rfd1R::new(((self.bits >> 5) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 3 - Receive FIFO1 full"]
    #[inline(always)]
    #[must_use]
    pub fn rff1(&mut self) -> Rff1W<Rfifo1Spec> {
        Rff1W::new(self, 3)
    }
    #[doc = "Bit 4 - Receive FIFO1 overfull"]
    #[inline(always)]
    #[must_use]
    pub fn rfo1(&mut self) -> Rfo1W<Rfifo1Spec> {
        Rfo1W::new(self, 4)
    }
    #[doc = "Bit 5 - Receive FIFO1 dequeue"]
    #[inline(always)]
    #[must_use]
    pub fn rfd1(&mut self) -> Rfd1W<Rfifo1Spec> {
        Rfd1W::new(self, 5)
    }
}
#[doc = "Receive message FIFO1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rfifo1::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`rfifo1::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Rfifo1Spec;
impl crate::RegisterSpec for Rfifo1Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rfifo1::R`](R) reader structure"]
impl crate::Readable for Rfifo1Spec {}
#[doc = "`write(|w| ..)` method takes [`rfifo1::W`](W) writer structure"]
impl crate::Writable for Rfifo1Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets RFIFO1 to value 0"]
impl crate::Resettable for Rfifo1Spec {
    const RESET_VALUE: u32 = 0;
}
