#[doc = "Register `RSQ0` reader"]
pub type R = crate::R<Rsq0Spec>;
#[doc = "Register `RSQ0` writer"]
pub type W = crate::W<Rsq0Spec>;
#[doc = "Field `RSQ12` reader - 13th conversion in regular sequence"]
pub type Rsq12R = crate::FieldReader;
#[doc = "Field `RSQ12` writer - 13th conversion in regular sequence"]
pub type Rsq12W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `RSQ13` reader - 14th conversion in regular sequence"]
pub type Rsq13R = crate::FieldReader;
#[doc = "Field `RSQ13` writer - 14th conversion in regular sequence"]
pub type Rsq13W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `RSQ14` reader - 15th conversion in regular sequence"]
pub type Rsq14R = crate::FieldReader;
#[doc = "Field `RSQ14` writer - 15th conversion in regular sequence"]
pub type Rsq14W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `RSQ15` reader - 16th conversion in regular sequence"]
pub type Rsq15R = crate::FieldReader;
#[doc = "Field `RSQ15` writer - 16th conversion in regular sequence"]
pub type Rsq15W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `RL` reader - Regular channel group length"]
pub type RlR = crate::FieldReader;
#[doc = "Field `RL` writer - Regular channel group length"]
pub type RlW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bits 0:4 - 13th conversion in regular sequence"]
    #[inline(always)]
    pub fn rsq12(&self) -> Rsq12R {
        Rsq12R::new((self.bits & 0x1f) as u8)
    }
    #[doc = "Bits 5:9 - 14th conversion in regular sequence"]
    #[inline(always)]
    pub fn rsq13(&self) -> Rsq13R {
        Rsq13R::new(((self.bits >> 5) & 0x1f) as u8)
    }
    #[doc = "Bits 10:14 - 15th conversion in regular sequence"]
    #[inline(always)]
    pub fn rsq14(&self) -> Rsq14R {
        Rsq14R::new(((self.bits >> 10) & 0x1f) as u8)
    }
    #[doc = "Bits 15:19 - 16th conversion in regular sequence"]
    #[inline(always)]
    pub fn rsq15(&self) -> Rsq15R {
        Rsq15R::new(((self.bits >> 15) & 0x1f) as u8)
    }
    #[doc = "Bits 20:23 - Regular channel group length"]
    #[inline(always)]
    pub fn rl(&self) -> RlR {
        RlR::new(((self.bits >> 20) & 0x0f) as u8)
    }
}
impl W {
    #[doc = "Bits 0:4 - 13th conversion in regular sequence"]
    #[inline(always)]
    #[must_use]
    pub fn rsq12(&mut self) -> Rsq12W<Rsq0Spec> {
        Rsq12W::new(self, 0)
    }
    #[doc = "Bits 5:9 - 14th conversion in regular sequence"]
    #[inline(always)]
    #[must_use]
    pub fn rsq13(&mut self) -> Rsq13W<Rsq0Spec> {
        Rsq13W::new(self, 5)
    }
    #[doc = "Bits 10:14 - 15th conversion in regular sequence"]
    #[inline(always)]
    #[must_use]
    pub fn rsq14(&mut self) -> Rsq14W<Rsq0Spec> {
        Rsq14W::new(self, 10)
    }
    #[doc = "Bits 15:19 - 16th conversion in regular sequence"]
    #[inline(always)]
    #[must_use]
    pub fn rsq15(&mut self) -> Rsq15W<Rsq0Spec> {
        Rsq15W::new(self, 15)
    }
    #[doc = "Bits 20:23 - Regular channel group length"]
    #[inline(always)]
    #[must_use]
    pub fn rl(&mut self) -> RlW<Rsq0Spec> {
        RlW::new(self, 20)
    }
}
#[doc = "regular sequence register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rsq0::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`rsq0::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Rsq0Spec;
impl crate::RegisterSpec for Rsq0Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rsq0::R`](R) reader structure"]
impl crate::Readable for Rsq0Spec {}
#[doc = "`write(|w| ..)` method takes [`rsq0::W`](W) writer structure"]
impl crate::Writable for Rsq0Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets RSQ0 to value 0"]
impl crate::Resettable for Rsq0Spec {
    const RESET_VALUE: u32 = 0;
}
