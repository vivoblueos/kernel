#[doc = "Register `IN_POP` reader"]
pub type R = crate::R<IN_POP_SPEC>;
#[doc = "Register `IN_POP` writer"]
pub type W = crate::W<IN_POP_SPEC>;
#[doc = "Field `INFIFO_RDATA` reader - This register stores the data popping from DMA FIFO."]
pub type INFIFO_RDATA_R = crate::FieldReader<u16>;
#[doc = "Field `INFIFO_POP` reader - Set this bit to pop data from DMA FIFO."]
pub type INFIFO_POP_R = crate::BitReader;
#[doc = "Field `INFIFO_POP` writer - Set this bit to pop data from DMA FIFO."]
pub type INFIFO_POP_W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:11 - This register stores the data popping from DMA FIFO."]
    #[inline(always)]
    pub fn infifo_rdata(&self) -> INFIFO_RDATA_R {
        INFIFO_RDATA_R::new((self.bits & 0x0fff) as u16)
    }
    #[doc = "Bit 12 - Set this bit to pop data from DMA FIFO."]
    #[inline(always)]
    pub fn infifo_pop(&self) -> INFIFO_POP_R {
        INFIFO_POP_R::new(((self.bits >> 12) & 1) != 0)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("IN_POP")
            .field("infifo_rdata", &self.infifo_rdata())
            .field("infifo_pop", &self.infifo_pop())
            .finish()
    }
}
impl W {
    #[doc = "Bit 12 - Set this bit to pop data from DMA FIFO."]
    #[inline(always)]
    pub fn infifo_pop(&mut self) -> INFIFO_POP_W<'_, IN_POP_SPEC> {
        INFIFO_POP_W::new(self, 12)
    }
}
#[doc = "DMA_IN_POP_CH0_REG.\n\nYou can [`read`](crate::Reg::read) this register and get [`in_pop::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`in_pop::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IN_POP_SPEC;
impl crate::RegisterSpec for IN_POP_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`in_pop::R`](R) reader structure"]
impl crate::Readable for IN_POP_SPEC {}
#[doc = "`write(|w| ..)` method takes [`in_pop::W`](W) writer structure"]
impl crate::Writable for IN_POP_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets IN_POP to value 0x0800"]
impl crate::Resettable for IN_POP_SPEC {
    const RESET_VALUE: u32 = 0x0800;
}
