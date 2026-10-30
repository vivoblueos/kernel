#[doc = "Register `RSQ2` reader"]
pub type R = crate::R<Rsq2Spec>;
#[doc = "Register `RSQ2` writer"]
pub type W = crate::W<Rsq2Spec>;
#[doc = "Field `RSQ0` reader - 1st conversion in regular sequence"]
pub type Rsq0R = crate::FieldReader;
#[doc = "Field `RSQ0` writer - 1st conversion in regular sequence"]
pub type Rsq0W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `RSQ1` reader - 2nd conversion in regular sequence"]
pub type Rsq1R = crate::FieldReader;
#[doc = "Field `RSQ1` writer - 2nd conversion in regular sequence"]
pub type Rsq1W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `RSQ2` reader - 3rd conversion in regular sequence"]
pub type Rsq2R = crate::FieldReader;
#[doc = "Field `RSQ2` writer - 3rd conversion in regular sequence"]
pub type Rsq2W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `RSQ3` reader - 4th conversion in regular sequence"]
pub type Rsq3R = crate::FieldReader;
#[doc = "Field `RSQ3` writer - 4th conversion in regular sequence"]
pub type Rsq3W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `RSQ4` reader - 5th conversion in regular sequence"]
pub type Rsq4R = crate::FieldReader;
#[doc = "Field `RSQ4` writer - 5th conversion in regular sequence"]
pub type Rsq4W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `RSQ5` reader - 6th conversion in regular sequence"]
pub type Rsq5R = crate::FieldReader;
#[doc = "Field `RSQ5` writer - 6th conversion in regular sequence"]
pub type Rsq5W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
impl R {
    #[doc = "Bits 0:4 - 1st conversion in regular sequence"]
    #[inline(always)]
    pub fn rsq0(&self) -> Rsq0R {
        Rsq0R::new((self.bits & 0x1f) as u8)
    }
    #[doc = "Bits 5:9 - 2nd conversion in regular sequence"]
    #[inline(always)]
    pub fn rsq1(&self) -> Rsq1R {
        Rsq1R::new(((self.bits >> 5) & 0x1f) as u8)
    }
    #[doc = "Bits 10:14 - 3rd conversion in regular sequence"]
    #[inline(always)]
    pub fn rsq2(&self) -> Rsq2R {
        Rsq2R::new(((self.bits >> 10) & 0x1f) as u8)
    }
    #[doc = "Bits 15:19 - 4th conversion in regular sequence"]
    #[inline(always)]
    pub fn rsq3(&self) -> Rsq3R {
        Rsq3R::new(((self.bits >> 15) & 0x1f) as u8)
    }
    #[doc = "Bits 20:24 - 5th conversion in regular sequence"]
    #[inline(always)]
    pub fn rsq4(&self) -> Rsq4R {
        Rsq4R::new(((self.bits >> 20) & 0x1f) as u8)
    }
    #[doc = "Bits 25:29 - 6th conversion in regular sequence"]
    #[inline(always)]
    pub fn rsq5(&self) -> Rsq5R {
        Rsq5R::new(((self.bits >> 25) & 0x1f) as u8)
    }
}
impl W {
    #[doc = "Bits 0:4 - 1st conversion in regular sequence"]
    #[inline(always)]
    #[must_use]
    pub fn rsq0(&mut self) -> Rsq0W<Rsq2Spec> {
        Rsq0W::new(self, 0)
    }
    #[doc = "Bits 5:9 - 2nd conversion in regular sequence"]
    #[inline(always)]
    #[must_use]
    pub fn rsq1(&mut self) -> Rsq1W<Rsq2Spec> {
        Rsq1W::new(self, 5)
    }
    #[doc = "Bits 10:14 - 3rd conversion in regular sequence"]
    #[inline(always)]
    #[must_use]
    pub fn rsq2(&mut self) -> Rsq2W<Rsq2Spec> {
        Rsq2W::new(self, 10)
    }
    #[doc = "Bits 15:19 - 4th conversion in regular sequence"]
    #[inline(always)]
    #[must_use]
    pub fn rsq3(&mut self) -> Rsq3W<Rsq2Spec> {
        Rsq3W::new(self, 15)
    }
    #[doc = "Bits 20:24 - 5th conversion in regular sequence"]
    #[inline(always)]
    #[must_use]
    pub fn rsq4(&mut self) -> Rsq4W<Rsq2Spec> {
        Rsq4W::new(self, 20)
    }
    #[doc = "Bits 25:29 - 6th conversion in regular sequence"]
    #[inline(always)]
    #[must_use]
    pub fn rsq5(&mut self) -> Rsq5W<Rsq2Spec> {
        Rsq5W::new(self, 25)
    }
}
#[doc = "regular sequence register 2\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rsq2::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`rsq2::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Rsq2Spec;
impl crate::RegisterSpec for Rsq2Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rsq2::R`](R) reader structure"]
impl crate::Readable for Rsq2Spec {}
#[doc = "`write(|w| ..)` method takes [`rsq2::W`](W) writer structure"]
impl crate::Writable for Rsq2Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets RSQ2 to value 0"]
impl crate::Resettable for Rsq2Spec {
    const RESET_VALUE: u32 = 0;
}
