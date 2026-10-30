#[doc = "Register `EXTISS0` reader"]
pub type R = crate::R<Extiss0Spec>;
#[doc = "Register `EXTISS0` writer"]
pub type W = crate::W<Extiss0Spec>;
#[doc = "Field `EXTI0_SS` reader - EXTI 0 sources selection"]
pub type Exti0SsR = crate::FieldReader;
#[doc = "Field `EXTI0_SS` writer - EXTI 0 sources selection"]
pub type Exti0SsW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `EXTI1_SS` reader - EXTI 1 sources selection"]
pub type Exti1SsR = crate::FieldReader;
#[doc = "Field `EXTI1_SS` writer - EXTI 1 sources selection"]
pub type Exti1SsW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `EXTI2_SS` reader - EXTI 2 sources selection"]
pub type Exti2SsR = crate::FieldReader;
#[doc = "Field `EXTI2_SS` writer - EXTI 2 sources selection"]
pub type Exti2SsW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `EXTI3_SS` reader - EXTI 3 sources selection"]
pub type Exti3SsR = crate::FieldReader;
#[doc = "Field `EXTI3_SS` writer - EXTI 3 sources selection"]
pub type Exti3SsW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bits 0:3 - EXTI 0 sources selection"]
    #[inline(always)]
    pub fn exti0_ss(&self) -> Exti0SsR {
        Exti0SsR::new((self.bits & 0x0f) as u8)
    }
    #[doc = "Bits 4:7 - EXTI 1 sources selection"]
    #[inline(always)]
    pub fn exti1_ss(&self) -> Exti1SsR {
        Exti1SsR::new(((self.bits >> 4) & 0x0f) as u8)
    }
    #[doc = "Bits 8:11 - EXTI 2 sources selection"]
    #[inline(always)]
    pub fn exti2_ss(&self) -> Exti2SsR {
        Exti2SsR::new(((self.bits >> 8) & 0x0f) as u8)
    }
    #[doc = "Bits 12:15 - EXTI 3 sources selection"]
    #[inline(always)]
    pub fn exti3_ss(&self) -> Exti3SsR {
        Exti3SsR::new(((self.bits >> 12) & 0x0f) as u8)
    }
}
impl W {
    #[doc = "Bits 0:3 - EXTI 0 sources selection"]
    #[inline(always)]
    #[must_use]
    pub fn exti0_ss(&mut self) -> Exti0SsW<Extiss0Spec> {
        Exti0SsW::new(self, 0)
    }
    #[doc = "Bits 4:7 - EXTI 1 sources selection"]
    #[inline(always)]
    #[must_use]
    pub fn exti1_ss(&mut self) -> Exti1SsW<Extiss0Spec> {
        Exti1SsW::new(self, 4)
    }
    #[doc = "Bits 8:11 - EXTI 2 sources selection"]
    #[inline(always)]
    #[must_use]
    pub fn exti2_ss(&mut self) -> Exti2SsW<Extiss0Spec> {
        Exti2SsW::new(self, 8)
    }
    #[doc = "Bits 12:15 - EXTI 3 sources selection"]
    #[inline(always)]
    #[must_use]
    pub fn exti3_ss(&mut self) -> Exti3SsW<Extiss0Spec> {
        Exti3SsW::new(self, 12)
    }
}
#[doc = "EXTI sources selection register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`extiss0::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`extiss0::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Extiss0Spec;
impl crate::RegisterSpec for Extiss0Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`extiss0::R`](R) reader structure"]
impl crate::Readable for Extiss0Spec {}
#[doc = "`write(|w| ..)` method takes [`extiss0::W`](W) writer structure"]
impl crate::Writable for Extiss0Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets EXTISS0 to value 0"]
impl crate::Resettable for Extiss0Spec {
    const RESET_VALUE: u32 = 0;
}
