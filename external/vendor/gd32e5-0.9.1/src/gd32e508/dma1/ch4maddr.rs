#[doc = "Register `CH4MADDR` reader"]
pub type R = crate::R<Ch4maddrSpec>;
#[doc = "Register `CH4MADDR` writer"]
pub type W = crate::W<Ch4maddrSpec>;
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
    pub fn maddr(&mut self) -> MaddrW<Ch4maddrSpec> {
        MaddrW::new(self, 0)
    }
}
#[doc = "Channel 4 memory base address register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ch4maddr::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ch4maddr::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Ch4maddrSpec;
impl crate::RegisterSpec for Ch4maddrSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ch4maddr::R`](R) reader structure"]
impl crate::Readable for Ch4maddrSpec {}
#[doc = "`write(|w| ..)` method takes [`ch4maddr::W`](W) writer structure"]
impl crate::Writable for Ch4maddrSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets CH4MADDR to value 0"]
impl crate::Resettable for Ch4maddrSpec {
    const RESET_VALUE: u32 = 0;
}
