#[doc = "Register `DIEP1TFLEN` reader"]
pub type R = crate::R<Diep1tflenSpec>;
#[doc = "Register `DIEP1TFLEN` writer"]
pub type W = crate::W<Diep1tflenSpec>;
#[doc = "Field `IEPTXRSAR` reader - IN endpoint FIFO transmit RAM start address"]
pub type IeptxrsarR = crate::FieldReader<u16>;
#[doc = "Field `IEPTXRSAR` writer - IN endpoint FIFO transmit RAM start address"]
pub type IeptxrsarW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
#[doc = "Field `IEPTXFD` reader - IN endpoint TxFIFO depth"]
pub type IeptxfdR = crate::FieldReader<u16>;
#[doc = "Field `IEPTXFD` writer - IN endpoint TxFIFO depth"]
pub type IeptxfdW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15 - IN endpoint FIFO transmit RAM start address"]
    #[inline(always)]
    pub fn ieptxrsar(&self) -> IeptxrsarR {
        IeptxrsarR::new((self.bits & 0xffff) as u16)
    }
    #[doc = "Bits 16:31 - IN endpoint TxFIFO depth"]
    #[inline(always)]
    pub fn ieptxfd(&self) -> IeptxfdR {
        IeptxfdR::new(((self.bits >> 16) & 0xffff) as u16)
    }
}
impl W {
    #[doc = "Bits 0:15 - IN endpoint FIFO transmit RAM start address"]
    #[inline(always)]
    #[must_use]
    pub fn ieptxrsar(&mut self) -> IeptxrsarW<Diep1tflenSpec> {
        IeptxrsarW::new(self, 0)
    }
    #[doc = "Bits 16:31 - IN endpoint TxFIFO depth"]
    #[inline(always)]
    #[must_use]
    pub fn ieptxfd(&mut self) -> IeptxfdW<Diep1tflenSpec> {
        IeptxfdW::new(self, 16)
    }
}
#[doc = "device IN endpoint transmit FIFO size register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep1tflen::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep1tflen::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Diep1tflenSpec;
impl crate::RegisterSpec for Diep1tflenSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`diep1tflen::R`](R) reader structure"]
impl crate::Readable for Diep1tflenSpec {}
#[doc = "`write(|w| ..)` method takes [`diep1tflen::W`](W) writer structure"]
impl crate::Writable for Diep1tflenSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DIEP1TFLEN to value 0x0200_0400"]
impl crate::Resettable for Diep1tflenSpec {
    const RESET_VALUE: u32 = 0x0200_0400;
}
