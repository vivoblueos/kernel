#[doc = "Register `RSQ1` reader"]
pub type R = crate::R<Rsq1Spec>;
#[doc = "Register `RSQ1` writer"]
pub type W = crate::W<Rsq1Spec>;
#[doc = "Field `RSQ6` reader - 7th conversion in regular sequence"]
pub type Rsq6R = crate::FieldReader;
#[doc = "Field `RSQ6` writer - 7th conversion in regular sequence"]
pub type Rsq6W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `RSQ7` reader - 8th conversion in regular sequence"]
pub type Rsq7R = crate::FieldReader;
#[doc = "Field `RSQ7` writer - 8th conversion in regular sequence"]
pub type Rsq7W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `RSQ8` reader - 9th conversion in regular sequence"]
pub type Rsq8R = crate::FieldReader;
#[doc = "Field `RSQ8` writer - 9th conversion in regular sequence"]
pub type Rsq8W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `RSQ9` reader - 10th conversion in regular sequence"]
pub type Rsq9R = crate::FieldReader;
#[doc = "Field `RSQ9` writer - 10th conversion in regular sequence"]
pub type Rsq9W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `RSQ10` reader - 11th conversion in regular sequence"]
pub type Rsq10R = crate::FieldReader;
#[doc = "Field `RSQ10` writer - 11th conversion in regular sequence"]
pub type Rsq10W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `RSQ11` reader - 12th conversion in regular sequence"]
pub type Rsq11R = crate::FieldReader;
#[doc = "Field `RSQ11` writer - 12th conversion in regular sequence"]
pub type Rsq11W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
impl R {
    #[doc = "Bits 0:4 - 7th conversion in regular sequence"]
    #[inline(always)]
    pub fn rsq6(&self) -> Rsq6R {
        Rsq6R::new((self.bits & 0x1f) as u8)
    }
    #[doc = "Bits 5:9 - 8th conversion in regular sequence"]
    #[inline(always)]
    pub fn rsq7(&self) -> Rsq7R {
        Rsq7R::new(((self.bits >> 5) & 0x1f) as u8)
    }
    #[doc = "Bits 10:14 - 9th conversion in regular sequence"]
    #[inline(always)]
    pub fn rsq8(&self) -> Rsq8R {
        Rsq8R::new(((self.bits >> 10) & 0x1f) as u8)
    }
    #[doc = "Bits 15:19 - 10th conversion in regular sequence"]
    #[inline(always)]
    pub fn rsq9(&self) -> Rsq9R {
        Rsq9R::new(((self.bits >> 15) & 0x1f) as u8)
    }
    #[doc = "Bits 20:24 - 11th conversion in regular sequence"]
    #[inline(always)]
    pub fn rsq10(&self) -> Rsq10R {
        Rsq10R::new(((self.bits >> 20) & 0x1f) as u8)
    }
    #[doc = "Bits 25:29 - 12th conversion in regular sequence"]
    #[inline(always)]
    pub fn rsq11(&self) -> Rsq11R {
        Rsq11R::new(((self.bits >> 25) & 0x1f) as u8)
    }
}
impl W {
    #[doc = "Bits 0:4 - 7th conversion in regular sequence"]
    #[inline(always)]
    #[must_use]
    pub fn rsq6(&mut self) -> Rsq6W<Rsq1Spec> {
        Rsq6W::new(self, 0)
    }
    #[doc = "Bits 5:9 - 8th conversion in regular sequence"]
    #[inline(always)]
    #[must_use]
    pub fn rsq7(&mut self) -> Rsq7W<Rsq1Spec> {
        Rsq7W::new(self, 5)
    }
    #[doc = "Bits 10:14 - 9th conversion in regular sequence"]
    #[inline(always)]
    #[must_use]
    pub fn rsq8(&mut self) -> Rsq8W<Rsq1Spec> {
        Rsq8W::new(self, 10)
    }
    #[doc = "Bits 15:19 - 10th conversion in regular sequence"]
    #[inline(always)]
    #[must_use]
    pub fn rsq9(&mut self) -> Rsq9W<Rsq1Spec> {
        Rsq9W::new(self, 15)
    }
    #[doc = "Bits 20:24 - 11th conversion in regular sequence"]
    #[inline(always)]
    #[must_use]
    pub fn rsq10(&mut self) -> Rsq10W<Rsq1Spec> {
        Rsq10W::new(self, 20)
    }
    #[doc = "Bits 25:29 - 12th conversion in regular sequence"]
    #[inline(always)]
    #[must_use]
    pub fn rsq11(&mut self) -> Rsq11W<Rsq1Spec> {
        Rsq11W::new(self, 25)
    }
}
#[doc = "regular sequence register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rsq1::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`rsq1::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Rsq1Spec;
impl crate::RegisterSpec for Rsq1Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rsq1::R`](R) reader structure"]
impl crate::Readable for Rsq1Spec {}
#[doc = "`write(|w| ..)` method takes [`rsq1::W`](W) writer structure"]
impl crate::Writable for Rsq1Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets RSQ1 to value 0"]
impl crate::Resettable for Rsq1Spec {
    const RESET_VALUE: u32 = 0;
}
