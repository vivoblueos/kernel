#[doc = "Register `FDATA` reader"]
pub type R = crate::R<FdataSpec>;
#[doc = "Register `FDATA` writer"]
pub type W = crate::W<FdataSpec>;
#[doc = "Field `FDATA` reader - Free Data Register bits"]
pub type FdataR = crate::FieldReader;
#[doc = "Field `FDATA` writer - Free Data Register bits"]
pub type FdataW<'a, REG> = crate::FieldWriterSafe<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - Free Data Register bits"]
    #[inline(always)]
    pub fn fdata(&self) -> FdataR {
        FdataR::new((self.bits & 0xff) as u8)
    }
}
impl W {
    #[doc = "Bits 0:7 - Free Data Register bits"]
    #[inline(always)]
    #[must_use]
    pub fn fdata(&mut self) -> FdataW<FdataSpec> {
        FdataW::new(self, 0)
    }
}
#[doc = "Free data register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`fdata::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`fdata::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct FdataSpec;
impl crate::RegisterSpec for FdataSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`fdata::R`](R) reader structure"]
impl crate::Readable for FdataSpec {}
#[doc = "`write(|w| ..)` method takes [`fdata::W`](W) writer structure"]
impl crate::Writable for FdataSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets FDATA to value 0"]
impl crate::Resettable for FdataSpec {
    const RESET_VALUE: u32 = 0;
}
