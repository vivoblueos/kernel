#[doc = "Register `IDATA1` reader"]
pub type R = crate::R<Idata1Spec>;
#[doc = "Register `IDATA1` writer"]
pub type W = crate::W<Idata1Spec>;
#[doc = "Field `IDATA1` reader - IDATA1"]
pub type Idata1R = crate::FieldReader<u32>;
#[doc = "Field `IDATA1` writer - IDATA1"]
pub type Idata1W<'a, REG> = crate::FieldWriter<'a, REG, 32, u32>;
impl R {
    #[doc = "Bits 0:31 - IDATA1"]
    #[inline(always)]
    pub fn idata1(&self) -> Idata1R {
        Idata1R::new(self.bits)
    }
}
impl W {
    #[doc = "Bits 0:31 - IDATA1"]
    #[inline(always)]
    #[must_use]
    pub fn idata1(&mut self) -> Idata1W<Idata1Spec> {
        Idata1W::new(self, 0)
    }
}
#[doc = "Input data1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`idata1::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`idata1::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Idata1Spec;
impl crate::RegisterSpec for Idata1Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`idata1::R`](R) reader structure"]
impl crate::Readable for Idata1Spec {}
#[doc = "`write(|w| ..)` method takes [`idata1::W`](W) writer structure"]
impl crate::Writable for Idata1Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets IDATA1 to value 0x3f80_0000"]
impl crate::Resettable for Idata1Spec {
    const RESET_VALUE: u32 = 0x3f80_0000;
}
