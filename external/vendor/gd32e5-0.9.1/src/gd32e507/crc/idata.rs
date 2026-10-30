#[doc = "Register `IDATA` reader"]
pub type R = crate::R<IdataSpec>;
#[doc = "Register `IDATA` writer"]
pub type W = crate::W<IdataSpec>;
#[doc = "Field `IDATA` reader - Configurable initial CRC data value"]
pub type IdataR = crate::FieldReader<u32>;
#[doc = "Field `IDATA` writer - Configurable initial CRC data value"]
pub type IdataW<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - Configurable initial CRC data value"]
    #[inline(always)]
    pub fn idata(&self) -> IdataR {
        IdataR::new(self.bits)
    }
}
impl W {
    #[doc = "Bits 0:31 - Configurable initial CRC data value"]
    #[inline(always)]
    #[must_use]
    pub fn idata(&mut self) -> IdataW<IdataSpec> {
        IdataW::new(self, 0)
    }
}
#[doc = "Initialization data register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`idata::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`idata::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IdataSpec;
impl crate::RegisterSpec for IdataSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`idata::R`](R) reader structure"]
impl crate::Readable for IdataSpec {}
#[doc = "`write(|w| ..)` method takes [`idata::W`](W) writer structure"]
impl crate::Writable for IdataSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets IDATA to value 0xffff_ffff"]
impl crate::Resettable for IdataSpec {
    const RESET_VALUE: u32 = 0xffff_ffff;
}
