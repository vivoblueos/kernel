#[doc = "Register `DATALEN` reader"]
pub type R = crate::R<DatalenSpec>;
#[doc = "Register `DATALEN` writer"]
pub type W = crate::W<DatalenSpec>;
#[doc = "Field `DATALEN` reader - Data transfer length"]
pub type DatalenR = crate::FieldReader<u32>;
#[doc = "Field `DATALEN` writer - Data transfer length"]
pub type DatalenW<'a, REG> = crate::FieldWriter<'a, REG, 25, u32>;
impl R {
    #[doc = "Bits 0:24 - Data transfer length"]
    #[inline(always)]
    pub fn datalen(&self) -> DatalenR {
        DatalenR::new(self.bits & 0x01ff_ffff)
    }
}
impl W {
    #[doc = "Bits 0:24 - Data transfer length"]
    #[inline(always)]
    #[must_use]
    pub fn datalen(&mut self) -> DatalenW<DatalenSpec> {
        DatalenW::new(self, 0)
    }
}
#[doc = "Data length register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`datalen::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`datalen::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DatalenSpec;
impl crate::RegisterSpec for DatalenSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`datalen::R`](R) reader structure"]
impl crate::Readable for DatalenSpec {}
#[doc = "`write(|w| ..)` method takes [`datalen::W`](W) writer structure"]
impl crate::Writable for DatalenSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DATALEN to value 0"]
impl crate::Resettable for DatalenSpec {
    const RESET_VALUE: u32 = 0;
}
