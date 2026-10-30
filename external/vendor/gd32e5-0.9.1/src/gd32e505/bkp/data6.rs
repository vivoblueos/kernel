#[doc = "Register `DATA6` reader"]
pub type R = crate::R<Data6Spec>;
#[doc = "Register `DATA6` writer"]
pub type W = crate::W<Data6Spec>;
#[doc = "Field `DATA` reader - Backup data"]
pub type DataR = crate::FieldReader<u16>;
#[doc = "Field `DATA` writer - Backup data"]
pub type DataW<'a, REG> = crate::FieldWriter<'a, REG, 16, u16>;
impl R {
    #[doc = "Bits 0:15 - Backup data"]
    #[inline(always)]
    pub fn data(&self) -> DataR {
        DataR::new(self.bits)
    }
}
impl W {
    #[doc = "Bits 0:15 - Backup data"]
    #[inline(always)]
    #[must_use]
    pub fn data(&mut self) -> DataW<Data6Spec> {
        DataW::new(self, 0)
    }
}
#[doc = "Backup data register 6\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data6::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data6::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Data6Spec;
impl crate::RegisterSpec for Data6Spec {
    type Ux = u16;
}
#[doc = "`read()` method returns [`data6::R`](R) reader structure"]
impl crate::Readable for Data6Spec {}
#[doc = "`write(|w| ..)` method takes [`data6::W`](W) writer structure"]
impl crate::Writable for Data6Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u16 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u16 = 0;
}
#[doc = "`reset()` method sets DATA6 to value 0"]
impl crate::Resettable for Data6Spec {
    const RESET_VALUE: u16 = 0;
}
