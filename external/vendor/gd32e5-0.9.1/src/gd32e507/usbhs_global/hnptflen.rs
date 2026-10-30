#[doc = "Register `HNPTFLEN` reader"]
pub type R = crate::R<HnptflenSpec>;
#[doc = "Register `HNPTFLEN` writer"]
pub type W = crate::W<HnptflenSpec>;
#[doc = "Field `HNPTXRSAR` reader - host non-periodic transmit Tx RAM start address"]
pub type HnptxrsarR = crate::FieldReader<u16>;
#[doc = "Field `HNPTXRSAR` writer - host non-periodic transmit Tx RAM start address"]
pub type HnptxrsarW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
#[doc = "Field `HNPTXFD` reader - host non-periodic TxFIFO depth"]
pub type HnptxfdR = crate::FieldReader<u16>;
#[doc = "Field `HNPTXFD` writer - host non-periodic TxFIFO depth"]
pub type HnptxfdW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15 - host non-periodic transmit Tx RAM start address"]
    #[inline(always)]
    pub fn hnptxrsar(&self) -> HnptxrsarR {
        HnptxrsarR::new((self.bits & 0xffff) as u16)
    }
    #[doc = "Bits 16:31 - host non-periodic TxFIFO depth"]
    #[inline(always)]
    pub fn hnptxfd(&self) -> HnptxfdR {
        HnptxfdR::new(((self.bits >> 16) & 0xffff) as u16)
    }
}
impl W {
    #[doc = "Bits 0:15 - host non-periodic transmit Tx RAM start address"]
    #[inline(always)]
    #[must_use]
    pub fn hnptxrsar(&mut self) -> HnptxrsarW<HnptflenSpec> {
        HnptxrsarW::new(self, 0)
    }
    #[doc = "Bits 16:31 - host non-periodic TxFIFO depth"]
    #[inline(always)]
    #[must_use]
    pub fn hnptxfd(&mut self) -> HnptxfdW<HnptflenSpec> {
        HnptxfdW::new(self, 16)
    }
}
#[doc = "Host non-periodic transmit FIFO length register (Host mode)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hnptflen::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hnptflen::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct HnptflenSpec;
impl crate::RegisterSpec for HnptflenSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`hnptflen::R`](R) reader structure"]
impl crate::Readable for HnptflenSpec {}
#[doc = "`write(|w| ..)` method takes [`hnptflen::W`](W) writer structure"]
impl crate::Writable for HnptflenSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets HNPTFLEN to value 0x0200_0200"]
impl crate::Resettable for HnptflenSpec {
    const RESET_VALUE: u32 = 0x0200_0200;
}
