#[doc = "Register `DIEP2DMAADDR` reader"]
pub type R = crate::R<Diep2dmaaddrSpec>;
#[doc = "Register `DIEP2DMAADDR` writer"]
pub type W = crate::W<Diep2dmaaddrSpec>;
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
    pub fn dmaaddr(&mut self) -> DmaaddrW<Diep2dmaaddrSpec> {
        DmaaddrW::new(self, 0)
    }
}
#[doc = "Device IN endpoint 2 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep2dmaaddr::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep2dmaaddr::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Diep2dmaaddrSpec;
impl crate::RegisterSpec for Diep2dmaaddrSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`diep2dmaaddr::R`](R) reader structure"]
impl crate::Readable for Diep2dmaaddrSpec {}
#[doc = "`write(|w| ..)` method takes [`diep2dmaaddr::W`](W) writer structure"]
impl crate::Writable for Diep2dmaaddrSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DIEP2DMAADDR to value 0"]
impl crate::Resettable for Diep2dmaaddrSpec {
    const RESET_VALUE: u32 = 0;
}
