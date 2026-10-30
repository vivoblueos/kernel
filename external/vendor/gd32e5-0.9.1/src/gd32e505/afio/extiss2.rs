#[doc = "Register `EXTISS2` reader"]
pub type R = crate::R<Extiss2Spec>;
#[doc = "Register `EXTISS2` writer"]
pub type W = crate::W<Extiss2Spec>;
#[doc = "Field `EXTI8_SS` reader - EXTI 8 sources selection"]
pub type Exti8SsR = crate::FieldReader;
#[doc = "Field `EXTI8_SS` writer - EXTI 8 sources selection"]
pub type Exti8SsW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `EXTI9_SS` reader - EXTI 9 sources selection"]
pub type Exti9SsR = crate::FieldReader;
#[doc = "Field `EXTI9_SS` writer - EXTI 9 sources selection"]
pub type Exti9SsW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `EXTI10_SS` reader - EXTI 10 sources selection"]
pub type Exti10SsR = crate::FieldReader;
#[doc = "Field `EXTI10_SS` writer - EXTI 10 sources selection"]
pub type Exti10SsW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `EXTI11_SS` reader - EXTI 11 sources selection"]
pub type Exti11SsR = crate::FieldReader;
#[doc = "Field `EXTI11_SS` writer - EXTI 11 sources selection"]
pub type Exti11SsW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bits 0:3 - EXTI 8 sources selection"]
    #[inline(always)]
    pub fn exti8_ss(&self) -> Exti8SsR {
        Exti8SsR::new((self.bits & 0x0f) as u8)
    }
    #[doc = "Bits 4:7 - EXTI 9 sources selection"]
    #[inline(always)]
    pub fn exti9_ss(&self) -> Exti9SsR {
        Exti9SsR::new(((self.bits >> 4) & 0x0f) as u8)
    }
    #[doc = "Bits 8:11 - EXTI 10 sources selection"]
    #[inline(always)]
    pub fn exti10_ss(&self) -> Exti10SsR {
        Exti10SsR::new(((self.bits >> 8) & 0x0f) as u8)
    }
    #[doc = "Bits 12:15 - EXTI 11 sources selection"]
    #[inline(always)]
    pub fn exti11_ss(&self) -> Exti11SsR {
        Exti11SsR::new(((self.bits >> 12) & 0x0f) as u8)
    }
}
impl W {
    #[doc = "Bits 0:3 - EXTI 8 sources selection"]
    #[inline(always)]
    #[must_use]
    pub fn exti8_ss(&mut self) -> Exti8SsW<Extiss2Spec> {
        Exti8SsW::new(self, 0)
    }
    #[doc = "Bits 4:7 - EXTI 9 sources selection"]
    #[inline(always)]
    #[must_use]
    pub fn exti9_ss(&mut self) -> Exti9SsW<Extiss2Spec> {
        Exti9SsW::new(self, 4)
    }
    #[doc = "Bits 8:11 - EXTI 10 sources selection"]
    #[inline(always)]
    #[must_use]
    pub fn exti10_ss(&mut self) -> Exti10SsW<Extiss2Spec> {
        Exti10SsW::new(self, 8)
    }
    #[doc = "Bits 12:15 - EXTI 11 sources selection"]
    #[inline(always)]
    #[must_use]
    pub fn exti11_ss(&mut self) -> Exti11SsW<Extiss2Spec> {
        Exti11SsW::new(self, 12)
    }
}
#[doc = "EXTI sources selection register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`extiss2::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`extiss2::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Extiss2Spec;
impl crate::RegisterSpec for Extiss2Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`extiss2::R`](R) reader structure"]
impl crate::Readable for Extiss2Spec {}
#[doc = "`write(|w| ..)` method takes [`extiss2::W`](W) writer structure"]
impl crate::Writable for Extiss2Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets EXTISS2 to value 0"]
impl crate::Resettable for Extiss2Spec {
    const RESET_VALUE: u32 = 0;
}
