#[doc = "Register `DIEP4TFLEN` reader"]
pub type R = crate::R<Diep4tflenSpec>;
#[doc = "Register `DIEP4TFLEN` writer"]
pub type W = crate::W<Diep4tflenSpec>;
#[doc = "Field `IEPTXRSAR` reader - IN endpoint FIFO4 transmit RAM start address"]
pub type IeptxrsarR = crate::FieldReader<u16>;
#[doc = "Field `IEPTXRSAR` writer - IN endpoint FIFO4 transmit RAM start address"]
pub type IeptxrsarW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
#[doc = "Field `IEPTXFD` reader - IN endpoint TxFIFO depth"]
pub type IeptxfdR = crate::FieldReader<u16>;
#[doc = "Field `IEPTXFD` writer - IN endpoint TxFIFO depth"]
pub type IeptxfdW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15 - IN endpoint FIFO4 transmit RAM start address"]
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
    #[doc = "Bits 0:15 - IN endpoint FIFO4 transmit RAM start address"]
    #[inline(always)]
    #[must_use]
    pub fn ieptxrsar(&mut self) -> IeptxrsarW<Diep4tflenSpec> {
        IeptxrsarW::new(self, 0)
    }
    #[doc = "Bits 16:31 - IN endpoint TxFIFO depth"]
    #[inline(always)]
    #[must_use]
    pub fn ieptxfd(&mut self) -> IeptxfdW<Diep4tflenSpec> {
        IeptxfdW::new(self, 16)
    }
}
#[doc = "device IN endpoint transmit FIFO size register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep4tflen::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep4tflen::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Diep4tflenSpec;
impl crate::RegisterSpec for Diep4tflenSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`diep4tflen::R`](R) reader structure"]
impl crate::Readable for Diep4tflenSpec {}
#[doc = "`write(|w| ..)` method takes [`diep4tflen::W`](W) writer structure"]
impl crate::Writable for Diep4tflenSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DIEP4TFLEN to value 0x0200_0400"]
impl crate::Resettable for Diep4tflenSpec {
    const RESET_VALUE: u32 = 0x0200_0400;
}
