#[doc = "Register `DMA_TDTADDR` reader"]
pub type R = crate::R<DmaTdtaddrSpec>;
#[doc = "Register `DMA_TDTADDR` writer"]
pub type W = crate::W<DmaTdtaddrSpec>;
#[doc = "Field `STT` reader - Start address of transmit table"]
pub type SttR = crate::FieldReader<u32>;
#[doc = "Field `STT` writer - Start address of transmit table"]
pub type SttW<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - Start address of transmit table"]
    #[inline(always)]
    pub fn stt(&self) -> SttR {
        SttR::new(self.bits)
    }
}
impl W {
    #[doc = "Bits 0:31 - Start address of transmit table"]
    #[inline(always)]
    #[must_use]
    pub fn stt(&mut self) -> SttW<DmaTdtaddrSpec> {
        SttW::new(self, 0)
    }
}
#[doc = "Ethernet DMA transmit descriptor table address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dma_tdtaddr::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dma_tdtaddr::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DmaTdtaddrSpec;
impl crate::RegisterSpec for DmaTdtaddrSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dma_tdtaddr::R`](R) reader structure"]
impl crate::Readable for DmaTdtaddrSpec {}
#[doc = "`write(|w| ..)` method takes [`dma_tdtaddr::W`](W) writer structure"]
impl crate::Writable for DmaTdtaddrSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DMA_TDTADDR to value 0"]
impl crate::Resettable for DmaTdtaddrSpec {
    const RESET_VALUE: u32 = 0;
}
