#[doc = "Register `DIEP3DMAADDR` reader"]
pub type R = crate::R<Diep3dmaaddrSpec>;
#[doc = "Register `DIEP3DMAADDR` writer"]
pub type W = crate::W<Diep3dmaaddrSpec>;
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
    pub fn dmaaddr(&mut self) -> DmaaddrW<Diep3dmaaddrSpec> {
        DmaaddrW::new(self, 0)
    }
}
#[doc = "Device IN endpoint 3 DMA address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep3dmaaddr::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep3dmaaddr::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Diep3dmaaddrSpec;
impl crate::RegisterSpec for Diep3dmaaddrSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`diep3dmaaddr::R`](R) reader structure"]
impl crate::Readable for Diep3dmaaddrSpec {}
#[doc = "`write(|w| ..)` method takes [`diep3dmaaddr::W`](W) writer structure"]
impl crate::Writable for Diep3dmaaddrSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DIEP3DMAADDR to value 0"]
impl crate::Resettable for Diep3dmaaddrSpec {
    const RESET_VALUE: u32 = 0;
}
