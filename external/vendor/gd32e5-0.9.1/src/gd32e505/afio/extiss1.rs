#[doc = "Register `EXTISS1` reader"]
pub type R = crate::R<Extiss1Spec>;
#[doc = "Register `EXTISS1` writer"]
pub type W = crate::W<Extiss1Spec>;
#[doc = "Field `EXTI4_SS` reader - EXTI 4 sources selection"]
pub type Exti4SsR = crate::FieldReader;
#[doc = "Field `EXTI4_SS` writer - EXTI 4 sources selection"]
pub type Exti4SsW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `EXTI5_SS` reader - EXTI 5 sources selection"]
pub type Exti5SsR = crate::FieldReader;
#[doc = "Field `EXTI5_SS` writer - EXTI 5 sources selection"]
pub type Exti5SsW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `EXTI6_SS` reader - EXTI 6 sources selection"]
pub type Exti6SsR = crate::FieldReader;
#[doc = "Field `EXTI6_SS` writer - EXTI 6 sources selection"]
pub type Exti6SsW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `EXTI7_SS` reader - EXTI 7 sources selection"]
pub type Exti7SsR = crate::FieldReader;
#[doc = "Field `EXTI7_SS` writer - EXTI 7 sources selection"]
pub type Exti7SsW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bits 0:3 - EXTI 4 sources selection"]
    #[inline(always)]
    pub fn exti4_ss(&self) -> Exti4SsR {
        Exti4SsR::new((self.bits & 0x0f) as u8)
    }
    #[doc = "Bits 4:7 - EXTI 5 sources selection"]
    #[inline(always)]
    pub fn exti5_ss(&self) -> Exti5SsR {
        Exti5SsR::new(((self.bits >> 4) & 0x0f) as u8)
    }
    #[doc = "Bits 8:11 - EXTI 6 sources selection"]
    #[inline(always)]
    pub fn exti6_ss(&self) -> Exti6SsR {
        Exti6SsR::new(((self.bits >> 8) & 0x0f) as u8)
    }
    #[doc = "Bits 12:15 - EXTI 7 sources selection"]
    #[inline(always)]
    pub fn exti7_ss(&self) -> Exti7SsR {
        Exti7SsR::new(((self.bits >> 12) & 0x0f) as u8)
    }
}
impl W {
    #[doc = "Bits 0:3 - EXTI 4 sources selection"]
    #[inline(always)]
    #[must_use]
    pub fn exti4_ss(&mut self) -> Exti4SsW<Extiss1Spec> {
        Exti4SsW::new(self, 0)
    }
    #[doc = "Bits 4:7 - EXTI 5 sources selection"]
    #[inline(always)]
    #[must_use]
    pub fn exti5_ss(&mut self) -> Exti5SsW<Extiss1Spec> {
        Exti5SsW::new(self, 4)
    }
    #[doc = "Bits 8:11 - EXTI 6 sources selection"]
    #[inline(always)]
    #[must_use]
    pub fn exti6_ss(&mut self) -> Exti6SsW<Extiss1Spec> {
        Exti6SsW::new(self, 8)
    }
    #[doc = "Bits 12:15 - EXTI 7 sources selection"]
    #[inline(always)]
    #[must_use]
    pub fn exti7_ss(&mut self) -> Exti7SsW<Extiss1Spec> {
        Exti7SsW::new(self, 12)
    }
}
#[doc = "EXTI sources selection register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`extiss1::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`extiss1::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Extiss1Spec;
impl crate::RegisterSpec for Extiss1Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`extiss1::R`](R) reader structure"]
impl crate::Readable for Extiss1Spec {}
#[doc = "`write(|w| ..)` method takes [`extiss1::W`](W) writer structure"]
impl crate::Writable for Extiss1Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets EXTISS1 to value 0"]
impl crate::Resettable for Extiss1Spec {
    const RESET_VALUE: u32 = 0;
}
