#[doc = "Register `FIFO` reader"]
pub type R = crate::R<FifoSpec>;
#[doc = "Register `FIFO` writer"]
pub type W = crate::W<FifoSpec>;
#[doc = "Field `FIFODT` reader - Receive FIFO data or transmit FIFO data"]
pub type FifodtR = crate::FieldReader<u32>;
#[doc = "Field `FIFODT` writer - Receive FIFO data or transmit FIFO data"]
pub type FifodtW<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - Receive FIFO data or transmit FIFO data"]
    #[inline(always)]
    pub fn fifodt(&self) -> FifodtR {
        FifodtR::new(self.bits)
    }
}
impl W {
    #[doc = "Bits 0:31 - Receive FIFO data or transmit FIFO data"]
    #[inline(always)]
    #[must_use]
    pub fn fifodt(&mut self) -> FifodtW<FifoSpec> {
        FifodtW::new(self, 0)
    }
}
#[doc = "FIFO data register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`fifo::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`fifo::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct FifoSpec;
impl crate::RegisterSpec for FifoSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`fifo::R`](R) reader structure"]
impl crate::Readable for FifoSpec {}
#[doc = "`write(|w| ..)` method takes [`fifo::W`](W) writer structure"]
impl crate::Writable for FifoSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets FIFO to value 0"]
impl crate::Resettable for FifoSpec {
    const RESET_VALUE: u32 = 0;
}
