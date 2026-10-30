#[doc = "Register `DOEP2DMAADDR` reader"]
pub type R = crate::R<Doep2dmaaddrSpec>;
#[doc = "Register `DOEP2DMAADDR` writer"]
pub type W = crate::W<Doep2dmaaddrSpec>;
#[doc = "Field `DMAADDR` reader - DMA address"]
pub type DmaaddrR = crate::FieldReader<u32>;
#[doc = "Field `DMAADDR` writer - DMA address"]
pub type DmaaddrW<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - DMA address"]
    #[inline(always)]
    pub fn dmaaddr(&self) -> DmaaddrR {
        DmaaddrR::new(self.bits)
    }
}
impl W {
    #[doc = "Bits 0:31 - DMA address"]
    #[inline(always)]
    #[must_use]
    pub fn dmaaddr(&mut self) -> DmaaddrW<Doep2dmaaddrSpec> {
        DmaaddrW::new(self, 0)
    }
}
#[doc = "Device OUT endpoint 2 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`doep2dmaaddr::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`doep2dmaaddr::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Doep2dmaaddrSpec;
impl crate::RegisterSpec for Doep2dmaaddrSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`doep2dmaaddr::R`](R) reader structure"]
impl crate::Readable for Doep2dmaaddrSpec {}
#[doc = "`write(|w| ..)` method takes [`doep2dmaaddr::W`](W) writer structure"]
impl crate::Writable for Doep2dmaaddrSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DOEP2DMAADDR to value 0"]
impl crate::Resettable for Doep2dmaaddrSpec {
    const RESET_VALUE: u32 = 0;
}
