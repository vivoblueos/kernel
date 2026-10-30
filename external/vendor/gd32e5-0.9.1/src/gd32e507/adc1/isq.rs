#[doc = "Register `ISQ` reader"]
pub type R = crate::R<IsqSpec>;
#[doc = "Register `ISQ` writer"]
pub type W = crate::W<IsqSpec>;
#[doc = "Field `ISQ0` reader - 1st conversion in inserted sequence"]
pub type Isq0R = crate::FieldReader;
#[doc = "Field `ISQ0` writer - 1st conversion in inserted sequence"]
pub type Isq0W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `ISQ1` reader - 2nd conversion in inserted sequence"]
pub type Isq1R = crate::FieldReader;
#[doc = "Field `ISQ1` writer - 2nd conversion in inserted sequence"]
pub type Isq1W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `ISQ2` reader - 3rd conversion in inserted sequence"]
pub type Isq2R = crate::FieldReader;
#[doc = "Field `ISQ2` writer - 3rd conversion in inserted sequence"]
pub type Isq2W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `ISQ3` reader - 4th conversion in inserted sequence"]
pub type Isq3R = crate::FieldReader;
#[doc = "Field `ISQ3` writer - 4th conversion in inserted sequence"]
pub type Isq3W<'a, REG> = crate::FieldWriter<'a, REG, 5>;
#[doc = "Field `IL` reader - Inserted channel group length"]
pub type IlR = crate::FieldReader;
#[doc = "Field `IL` writer - Inserted channel group length"]
pub type IlW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
impl R {
    #[doc = "Bits 0:4 - 1st conversion in inserted sequence"]
    #[inline(always)]
    pub fn isq0(&self) -> Isq0R {
        Isq0R::new((self.bits & 0x1f) as u8)
    }
    #[doc = "Bits 5:9 - 2nd conversion in inserted sequence"]
    #[inline(always)]
    pub fn isq1(&self) -> Isq1R {
        Isq1R::new(((self.bits >> 5) & 0x1f) as u8)
    }
    #[doc = "Bits 10:14 - 3rd conversion in inserted sequence"]
    #[inline(always)]
    pub fn isq2(&self) -> Isq2R {
        Isq2R::new(((self.bits >> 10) & 0x1f) as u8)
    }
    #[doc = "Bits 15:19 - 4th conversion in inserted sequence"]
    #[inline(always)]
    pub fn isq3(&self) -> Isq3R {
        Isq3R::new(((self.bits >> 15) & 0x1f) as u8)
    }
    #[doc = "Bits 20:21 - Inserted channel group length"]
    #[inline(always)]
    pub fn il(&self) -> IlR {
        IlR::new(((self.bits >> 20) & 3) as u8)
    }
}
impl W {
    #[doc = "Bits 0:4 - 1st conversion in inserted sequence"]
    #[inline(always)]
    #[must_use]
    pub fn isq0(&mut self) -> Isq0W<IsqSpec> {
        Isq0W::new(self, 0)
    }
    #[doc = "Bits 5:9 - 2nd conversion in inserted sequence"]
    #[inline(always)]
    #[must_use]
    pub fn isq1(&mut self) -> Isq1W<IsqSpec> {
        Isq1W::new(self, 5)
    }
    #[doc = "Bits 10:14 - 3rd conversion in inserted sequence"]
    #[inline(always)]
    #[must_use]
    pub fn isq2(&mut self) -> Isq2W<IsqSpec> {
        Isq2W::new(self, 10)
    }
    #[doc = "Bits 15:19 - 4th conversion in inserted sequence"]
    #[inline(always)]
    #[must_use]
    pub fn isq3(&mut self) -> Isq3W<IsqSpec> {
        Isq3W::new(self, 15)
    }
    #[doc = "Bits 20:21 - Inserted channel group length"]
    #[inline(always)]
    #[must_use]
    pub fn il(&mut self) -> IlW<IsqSpec> {
        IlW::new(self, 20)
    }
}
#[doc = "Inserted sequence register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`isq::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`isq::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IsqSpec;
impl crate::RegisterSpec for IsqSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`isq::R`](R) reader structure"]
impl crate::Readable for IsqSpec {}
#[doc = "`write(|w| ..)` method takes [`isq::W`](W) writer structure"]
impl crate::Writable for IsqSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets ISQ to value 0"]
impl crate::Resettable for IsqSpec {
    const RESET_VALUE: u32 = 0;
}
