#[doc = "Register `DATA3` reader"]
pub type R = crate::R<Data3Spec>;
#[doc = "Register `DATA3` writer"]
pub type W = crate::W<Data3Spec>;
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
    pub fn data(&mut self) -> DataW<Data3Spec> {
        DataW::new(self, 0)
    }
}
#[doc = "Backup data register 3\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`data3::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`data3::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Data3Spec;
impl crate::RegisterSpec for Data3Spec {
    type Ux = u16;
}
#[doc = "`read()` method returns [`data3::R`](R) reader structure"]
impl crate::Readable for Data3Spec {}
#[doc = "`write(|w| ..)` method takes [`data3::W`](W) writer structure"]
impl crate::Writable for Data3Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u16 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u16 = 0;
}
#[doc = "`reset()` method sets DATA3 to value 0"]
impl crate::Resettable for Data3Spec {
    const RESET_VALUE: u16 = 0;
}
