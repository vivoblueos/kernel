#[doc = "Register `DIEP0TFLEN` reader"]
pub type R = crate::R<Diep0tflenSpec>;
#[doc = "Register `DIEP0TFLEN` writer"]
pub type W = crate::W<Diep0tflenSpec>;
#[doc = "Field `IEP0TXRSAR` reader - in endpoint 0 Tx RAM start address"]
pub type Iep0txrsarR = crate::FieldReader<u16>;
#[doc = "Field `IEP0TXRSAR` writer - in endpoint 0 Tx RAM start address"]
pub type Iep0txrsarW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
#[doc = "Field `IEP0TXFD` reader - in endpoint 0 Tx FIFO depth"]
pub type Iep0txfdR = crate::FieldReader<u16>;
#[doc = "Field `IEP0TXFD` writer - in endpoint 0 Tx FIFO depth"]
pub type Iep0txfdW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15 - in endpoint 0 Tx RAM start address"]
    #[inline(always)]
    pub fn iep0txrsar(&self) -> Iep0txrsarR {
        Iep0txrsarR::new((self.bits & 0xffff) as u16)
    }
    #[doc = "Bits 16:31 - in endpoint 0 Tx FIFO depth"]
    #[inline(always)]
    pub fn iep0txfd(&self) -> Iep0txfdR {
        Iep0txfdR::new(((self.bits >> 16) & 0xffff) as u16)
    }
}
impl W {
    #[doc = "Bits 0:15 - in endpoint 0 Tx RAM start address"]
    #[inline(always)]
    #[must_use]
    pub fn iep0txrsar(&mut self) -> Iep0txrsarW<Diep0tflenSpec> {
        Iep0txrsarW::new(self, 0)
    }
    #[doc = "Bits 16:31 - in endpoint 0 Tx FIFO depth"]
    #[inline(always)]
    #[must_use]
    pub fn iep0txfd(&mut self) -> Iep0txfdW<Diep0tflenSpec> {
        Iep0txfdW::new(self, 16)
    }
}
#[doc = "Device IN endpoint 0 transmit FIFO length (Device mode)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep0tflen::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep0tflen::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Diep0tflenSpec;
impl crate::RegisterSpec for Diep0tflenSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`diep0tflen::R`](R) reader structure"]
impl crate::Readable for Diep0tflenSpec {}
#[doc = "`write(|w| ..)` method takes [`diep0tflen::W`](W) writer structure"]
impl crate::Writable for Diep0tflenSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DIEP0TFLEN to value 0x0200_0200"]
impl crate::Resettable for Diep0tflenSpec {
    const RESET_VALUE: u32 = 0x0200_0200;
}
