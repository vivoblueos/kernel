#[doc = "Register `SAMPT0` reader"]
pub type R = crate::R<Sampt0Spec>;
#[doc = "Register `SAMPT0` writer"]
pub type W = crate::W<Sampt0Spec>;
#[doc = "Field `SPT10` reader - Channel 10 sample time selection"]
pub type Spt10R = crate::FieldReader;
#[doc = "Field `SPT10` writer - Channel 10 sample time selection"]
pub type Spt10W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `SPT11` reader - Channel 11 sample time selection"]
pub type Spt11R = crate::FieldReader;
#[doc = "Field `SPT11` writer - Channel 11 sample time selection"]
pub type Spt11W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `SPT12` reader - Channel 12 sample time selection"]
pub type Spt12R = crate::FieldReader;
#[doc = "Field `SPT12` writer - Channel 12 sample time selection"]
pub type Spt12W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `SPT13` reader - Channel 13 sample time selection"]
pub type Spt13R = crate::FieldReader;
#[doc = "Field `SPT13` writer - Channel 13 sample time selection"]
pub type Spt13W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `SPT14` reader - Channel 14 sample time selection"]
pub type Spt14R = crate::FieldReader;
#[doc = "Field `SPT14` writer - Channel 14 sample time selection"]
pub type Spt14W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `SPT15` reader - Channel 15 sample time selection"]
pub type Spt15R = crate::FieldReader;
#[doc = "Field `SPT15` writer - Channel 15 sample time selection"]
pub type Spt15W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `SPT16` reader - Channel 16 sample time selection"]
pub type Spt16R = crate::FieldReader;
#[doc = "Field `SPT16` writer - Channel 16 sample time selection"]
pub type Spt16W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `SPT17` reader - Channel 17 sample time selection"]
pub type Spt17R = crate::FieldReader;
#[doc = "Field `SPT17` writer - Channel 17 sample time selection"]
pub type Spt17W<'a, REG> = crate::FieldWriter<'a, REG, 3>;
impl R {
    #[doc = "Bits 0:2 - Channel 10 sample time selection"]
    #[inline(always)]
    pub fn spt10(&self) -> Spt10R {
        Spt10R::new((self.bits & 7) as u8)
    }
    #[doc = "Bits 3:5 - Channel 11 sample time selection"]
    #[inline(always)]
    pub fn spt11(&self) -> Spt11R {
        Spt11R::new(((self.bits >> 3) & 7) as u8)
    }
    #[doc = "Bits 6:8 - Channel 12 sample time selection"]
    #[inline(always)]
    pub fn spt12(&self) -> Spt12R {
        Spt12R::new(((self.bits >> 6) & 7) as u8)
    }
    #[doc = "Bits 9:11 - Channel 13 sample time selection"]
    #[inline(always)]
    pub fn spt13(&self) -> Spt13R {
        Spt13R::new(((self.bits >> 9) & 7) as u8)
    }
    #[doc = "Bits 12:14 - Channel 14 sample time selection"]
    #[inline(always)]
    pub fn spt14(&self) -> Spt14R {
        Spt14R::new(((self.bits >> 12) & 7) as u8)
    }
    #[doc = "Bits 15:17 - Channel 15 sample time selection"]
    #[inline(always)]
    pub fn spt15(&self) -> Spt15R {
        Spt15R::new(((self.bits >> 15) & 7) as u8)
    }
    #[doc = "Bits 18:20 - Channel 16 sample time selection"]
    #[inline(always)]
    pub fn spt16(&self) -> Spt16R {
        Spt16R::new(((self.bits >> 18) & 7) as u8)
    }
    #[doc = "Bits 21:23 - Channel 17 sample time selection"]
    #[inline(always)]
    pub fn spt17(&self) -> Spt17R {
        Spt17R::new(((self.bits >> 21) & 7) as u8)
    }
}
impl W {
    #[doc = "Bits 0:2 - Channel 10 sample time selection"]
    #[inline(always)]
    #[must_use]
    pub fn spt10(&mut self) -> Spt10W<Sampt0Spec> {
        Spt10W::new(self, 0)
    }
    #[doc = "Bits 3:5 - Channel 11 sample time selection"]
    #[inline(always)]
    #[must_use]
    pub fn spt11(&mut self) -> Spt11W<Sampt0Spec> {
        Spt11W::new(self, 3)
    }
    #[doc = "Bits 6:8 - Channel 12 sample time selection"]
    #[inline(always)]
    #[must_use]
    pub fn spt12(&mut self) -> Spt12W<Sampt0Spec> {
        Spt12W::new(self, 6)
    }
    #[doc = "Bits 9:11 - Channel 13 sample time selection"]
    #[inline(always)]
    #[must_use]
    pub fn spt13(&mut self) -> Spt13W<Sampt0Spec> {
        Spt13W::new(self, 9)
    }
    #[doc = "Bits 12:14 - Channel 14 sample time selection"]
    #[inline(always)]
    #[must_use]
    pub fn spt14(&mut self) -> Spt14W<Sampt0Spec> {
        Spt14W::new(self, 12)
    }
    #[doc = "Bits 15:17 - Channel 15 sample time selection"]
    #[inline(always)]
    #[must_use]
    pub fn spt15(&mut self) -> Spt15W<Sampt0Spec> {
        Spt15W::new(self, 15)
    }
    #[doc = "Bits 18:20 - Channel 16 sample time selection"]
    #[inline(always)]
    #[must_use]
    pub fn spt16(&mut self) -> Spt16W<Sampt0Spec> {
        Spt16W::new(self, 18)
    }
    #[doc = "Bits 21:23 - Channel 17 sample time selection"]
    #[inline(always)]
    #[must_use]
    pub fn spt17(&mut self) -> Spt17W<Sampt0Spec> {
        Spt17W::new(self, 21)
    }
}
#[doc = "Sample time register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`sampt0::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`sampt0::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Sampt0Spec;
impl crate::RegisterSpec for Sampt0Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`sampt0::R`](R) reader structure"]
impl crate::Readable for Sampt0Spec {}
#[doc = "`write(|w| ..)` method takes [`sampt0::W`](W) writer structure"]
impl crate::Writable for Sampt0Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets SAMPT0 to value 0"]
impl crate::Resettable for Sampt0Spec {
    const RESET_VALUE: u32 = 0;
}
