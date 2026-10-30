#[doc = "Register `HCH9DMAADDR` reader"]
pub type R = crate::R<Hch9dmaaddrSpec>;
#[doc = "Register `HCH9DMAADDR` writer"]
pub type W = crate::W<Hch9dmaaddrSpec>;
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
    pub fn dmaaddr(&mut self) -> DmaaddrW<Hch9dmaaddrSpec> {
        DmaaddrW::new(self, 0)
    }
}
#[doc = "Host channel 9 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch9dmaaddr::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch9dmaaddr::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Hch9dmaaddrSpec;
impl crate::RegisterSpec for Hch9dmaaddrSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`hch9dmaaddr::R`](R) reader structure"]
impl crate::Readable for Hch9dmaaddrSpec {}
#[doc = "`write(|w| ..)` method takes [`hch9dmaaddr::W`](W) writer structure"]
impl crate::Writable for Hch9dmaaddrSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets HCH9DMAADDR to value 0"]
impl crate::Resettable for Hch9dmaaddrSpec {
    const RESET_VALUE: u32 = 0;
}
