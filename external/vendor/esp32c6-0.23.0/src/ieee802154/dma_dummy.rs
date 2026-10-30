#[doc = "Register `DMA_DUMMY` reader"]
pub type R = crate::R<DMA_DUMMY_SPEC>;
#[doc = "Register `DMA_DUMMY` writer"]
pub type W = crate::W<DMA_DUMMY_SPEC>;
#[doc = "Field `DATA` reader - "]
pub type DATA_R = crate::FieldReader<u32>;
#[doc = "Field `DATA` writer - "]
pub type DATA_W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31"]
    #[inline(always)]
    pub fn data(&self) -> DATA_R {
        DATA_R::new(self.bits)
    }
}
#[cfg(feature = "impl-register-debug")]
impl core::fmt::Debug for R {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        f.debug_struct("DMA_DUMMY")
            .field("data", &self.data())
            .finish()
    }
}
impl W {
    #[doc = "Bits 0:31"]
    #[inline(always)]
    pub fn data(&mut self) -> DATA_W<'_, DMA_DUMMY_SPEC> {
        DATA_W::new(self, 0)
    }
}
#[doc = "\n\nYou can [`read`](crate::Reg::read) this register and get [`dma_dummy::R`](R). You can [`reset`](crate::Reg::reset), [`write`](crate::Reg::write), [`write_with_zero`](crate::Reg::write_with_zero) this register using [`dma_dummy::W`](W). You can also [`modify`](crate::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DMA_DUMMY_SPEC;
impl crate::RegisterSpec for DMA_DUMMY_SPEC {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dma_dummy::R`](R) reader structure"]
impl crate::Readable for DMA_DUMMY_SPEC {}
#[doc = "`write(|w| ..)` method takes [`dma_dummy::W`](W) writer structure"]
impl crate::Writable for DMA_DUMMY_SPEC {
    type Safety = crate::Unsafe;
}
#[doc = "`reset()` method sets DMA_DUMMY to value 0"]
impl crate::Resettable for DMA_DUMMY_SPEC {}
