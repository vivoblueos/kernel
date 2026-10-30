#[doc = "Register `RFIFO0` reader"]
pub type R = crate::R<Rfifo0Spec>;
#[doc = "Register `RFIFO0` writer"]
pub type W = crate::W<Rfifo0Spec>;
#[doc = "Field `RFL0` reader - Receive FIFO0 length"]
pub type Rfl0R = crate::FieldReader;
#[doc = "Field `RFF0` reader - Receive FIFO0 full"]
pub type Rff0R = crate::BitReader;
#[doc = "Field `RFF0` writer - Receive FIFO0 full"]
pub type Rff0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RFO0` reader - Receive FIFO0 overfull"]
pub type Rfo0R = crate::BitReader;
#[doc = "Field `RFO0` writer - Receive FIFO0 overfull"]
pub type Rfo0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RFD0` reader - Receive FIFO0 dequeue"]
pub type Rfd0R = crate::BitReader;
#[doc = "Field `RFD0` writer - Receive FIFO0 dequeue"]
pub type Rfd0W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:1 - Receive FIFO0 length"]
    #[inline(always)]
    pub fn rfl0(&self) -> Rfl0R {
        Rfl0R::new((self.bits & 3) as u8)
    }
    #[doc = "Bit 3 - Receive FIFO0 full"]
    #[inline(always)]
    pub fn rff0(&self) -> Rff0R {
        Rff0R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Receive FIFO0 overfull"]
    #[inline(always)]
    pub fn rfo0(&self) -> Rfo0R {
        Rfo0R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Receive FIFO0 dequeue"]
    #[inline(always)]
    pub fn rfd0(&self) -> Rfd0R {
        Rfd0R::new(((self.bits >> 5) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 3 - Receive FIFO0 full"]
    #[inline(always)]
    #[must_use]
    pub fn rff0(&mut self) -> Rff0W<Rfifo0Spec> {
        Rff0W::new(self, 3)
    }
    #[doc = "Bit 4 - Receive FIFO0 overfull"]
    #[inline(always)]
    #[must_use]
    pub fn rfo0(&mut self) -> Rfo0W<Rfifo0Spec> {
        Rfo0W::new(self, 4)
    }
    #[doc = "Bit 5 - Receive FIFO0 dequeue"]
    #[inline(always)]
    #[must_use]
    pub fn rfd0(&mut self) -> Rfd0W<Rfifo0Spec> {
        Rfd0W::new(self, 5)
    }
}
#[doc = "Receive message FIFO0 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rfifo0::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`rfifo0::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Rfifo0Spec;
impl crate::RegisterSpec for Rfifo0Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rfifo0::R`](R) reader structure"]
impl crate::Readable for Rfifo0Spec {}
#[doc = "`write(|w| ..)` method takes [`rfifo0::W`](W) writer structure"]
impl crate::Writable for Rfifo0Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets RFIFO0 to value 0"]
impl crate::Resettable for Rfifo0Spec {
    const RESET_VALUE: u32 = 0;
}
