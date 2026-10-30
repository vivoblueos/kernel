#[doc = "Register `CH1PADDR` reader"]
pub type R = crate::R<Ch1paddrSpec>;
#[doc = "Register `CH1PADDR` writer"]
pub type W = crate::W<Ch1paddrSpec>;
#[doc = "Field `PADDR` reader - Peripheral base address"]
pub type PaddrR = crate::FieldReader<u32>;
#[doc = "Field `PADDR` writer - Peripheral base address"]
pub type PaddrW<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - Peripheral base address"]
    #[inline(always)]
    pub fn paddr(&self) -> PaddrR {
        PaddrR::new(self.bits)
    }
}
impl W {
    #[doc = "Bits 0:31 - Peripheral base address"]
    #[inline(always)]
    #[must_use]
    pub fn paddr(&mut self) -> PaddrW<Ch1paddrSpec> {
        PaddrW::new(self, 0)
    }
}
#[doc = "Channel 1 peripheral base address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch1paddr::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch1paddr::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ch1paddrSpec;
impl crate::RegisterSpec for Ch1paddrSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ch1paddr::R`](R) reader structure"]
impl crate::Readable for Ch1paddrSpec {}
#[doc = "`write(|w| ..)` method takes [`ch1paddr::W`](W) writer structure"]
impl crate::Writable for Ch1paddrSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CH1PADDR to value 0"]
impl crate::Resettable for Ch1paddrSpec {
    const RESET_VALUE: u32 = 0;
}
