#[doc = "Register `EXTISS3` reader"]
pub type R = crate::R<Extiss3Spec>;
#[doc = "Register `EXTISS3` writer"]
pub type W = crate::W<Extiss3Spec>;
#[doc = "Field `EXTI12_SS` reader - EXTI 12 sources selection"]
pub type Exti12SsR = crate::FieldReader;
#[doc = "Field `EXTI12_SS` writer - EXTI 12 sources selection"]
pub type Exti12SsW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `EXTI13_SS` reader - EXTI 13 sources selection"]
pub type Exti13SsR = crate::FieldReader;
#[doc = "Field `EXTI13_SS` writer - EXTI 13 sources selection"]
pub type Exti13SsW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `EXTI14_SS` reader - EXTI 14 sources selection"]
pub type Exti14SsR = crate::FieldReader;
#[doc = "Field `EXTI14_SS` writer - EXTI 14 sources selection"]
pub type Exti14SsW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `EXTI15_SS` reader - EXTI 15 sources selection"]
pub type Exti15SsR = crate::FieldReader;
#[doc = "Field `EXTI15_SS` writer - EXTI 15 sources selection"]
pub type Exti15SsW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bits 0:3 - EXTI 12 sources selection"]
    #[inline(always)]
    pub fn exti12_ss(&self) -> Exti12SsR {
        Exti12SsR::new((self.bits & 0x0f) as u8)
    }
    #[doc = "Bits 4:7 - EXTI 13 sources selection"]
    #[inline(always)]
    pub fn exti13_ss(&self) -> Exti13SsR {
        Exti13SsR::new(((self.bits >> 4) & 0x0f) as u8)
    }
    #[doc = "Bits 8:11 - EXTI 14 sources selection"]
    #[inline(always)]
    pub fn exti14_ss(&self) -> Exti14SsR {
        Exti14SsR::new(((self.bits >> 8) & 0x0f) as u8)
    }
    #[doc = "Bits 12:15 - EXTI 15 sources selection"]
    #[inline(always)]
    pub fn exti15_ss(&self) -> Exti15SsR {
        Exti15SsR::new(((self.bits >> 12) & 0x0f) as u8)
    }
}
impl W {
    #[doc = "Bits 0:3 - EXTI 12 sources selection"]
    #[inline(always)]
    #[must_use]
    pub fn exti12_ss(&mut self) -> Exti12SsW<Extiss3Spec> {
        Exti12SsW::new(self, 0)
    }
    #[doc = "Bits 4:7 - EXTI 13 sources selection"]
    #[inline(always)]
    #[must_use]
    pub fn exti13_ss(&mut self) -> Exti13SsW<Extiss3Spec> {
        Exti13SsW::new(self, 4)
    }
    #[doc = "Bits 8:11 - EXTI 14 sources selection"]
    #[inline(always)]
    #[must_use]
    pub fn exti14_ss(&mut self) -> Exti14SsW<Extiss3Spec> {
        Exti14SsW::new(self, 8)
    }
    #[doc = "Bits 12:15 - EXTI 15 sources selection"]
    #[inline(always)]
    #[must_use]
    pub fn exti15_ss(&mut self) -> Exti15SsW<Extiss3Spec> {
        Exti15SsW::new(self, 12)
    }
}
#[doc = "EXTI sources selection register 3\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`extiss3::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`extiss3::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Extiss3Spec;
impl crate::RegisterSpec for Extiss3Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`extiss3::R`](R) reader structure"]
impl crate::Readable for Extiss3Spec {}
#[doc = "`write(|w| ..)` method takes [`extiss3::W`](W) writer structure"]
impl crate::Writable for Extiss3Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets EXTISS3 to value 0"]
impl crate::Resettable for Extiss3Spec {
    const RESET_VALUE: u32 = 0;
}
