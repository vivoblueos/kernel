#[doc = "Register `CH3MADDR` reader"]
pub type R = crate::R<Ch3maddrSpec>;
#[doc = "Register `CH3MADDR` writer"]
pub type W = crate::W<Ch3maddrSpec>;
#[doc = "Field `MADDR` reader - Memory base address"]
pub type MaddrR = crate::FieldReader<u32>;
#[doc = "Field `MADDR` writer - Memory base address"]
pub type MaddrW<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - Memory base address"]
    #[inline(always)]
    pub fn maddr(&self) -> MaddrR {
        MaddrR::new(self.bits)
    }
}
impl W {
    #[doc = "Bits 0:31 - Memory base address"]
    #[inline(always)]
    #[must_use]
    pub fn maddr(&mut self) -> MaddrW<Ch3maddrSpec> {
        MaddrW::new(self, 0)
    }
}
#[doc = "Channel 3 memory base address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch3maddr::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch3maddr::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ch3maddrSpec;
impl crate::RegisterSpec for Ch3maddrSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ch3maddr::R`](R) reader structure"]
impl crate::Readable for Ch3maddrSpec {}
#[doc = "`write(|w| ..)` method takes [`ch3maddr::W`](W) writer structure"]
impl crate::Writable for Ch3maddrSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CH3MADDR to value 0"]
impl crate::Resettable for Ch3maddrSpec {
    const RESET_VALUE: u32 = 0;
}
