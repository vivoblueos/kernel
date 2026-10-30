#[doc = "Register `TMDATA10` reader"]
pub type R = crate::R<Tmdata10Spec>;
#[doc = "Register `TMDATA10` writer"]
pub type W = crate::W<Tmdata10Spec>;
#[doc = "Field `DB4` reader - Data byte 4"]
pub type Db4R = crate::FieldReader;
#[doc = "Field `DB4` writer - Data byte 4"]
pub type Db4W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `DB5` reader - Data byte 5"]
pub type Db5R = crate::FieldReader;
#[doc = "Field `DB5` writer - Data byte 5"]
pub type Db5W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `DB6` reader - Data byte 6"]
pub type Db6R = crate::FieldReader;
#[doc = "Field `DB6` writer - Data byte 6"]
pub type Db6W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
#[doc = "Field `DB7` reader - Data byte 7"]
pub type Db7R = crate::FieldReader;
#[doc = "Field `DB7` writer - Data byte 7"]
pub type Db7W<'a, REG> = crate::FieldWriter<'a, REG, 8>;
impl R {
    #[doc = "Bits 0:7 - Data byte 4"]
    #[inline(always)]
    pub fn db4(&self) -> Db4R {
        Db4R::new((self.bits & 0xff) as u8)
    }
    #[doc = "Bits 8:15 - Data byte 5"]
    #[inline(always)]
    pub fn db5(&self) -> Db5R {
        Db5R::new(((self.bits >> 8) & 0xff) as u8)
    }
    #[doc = "Bits 16:23 - Data byte 6"]
    #[inline(always)]
    pub fn db6(&self) -> Db6R {
        Db6R::new(((self.bits >> 16) & 0xff) as u8)
    }
    #[doc = "Bits 24:31 - Data byte 7"]
    #[inline(always)]
    pub fn db7(&self) -> Db7R {
        Db7R::new(((self.bits >> 24) & 0xff) as u8)
    }
}
impl W {
    #[doc = "Bits 0:7 - Data byte 4"]
    #[inline(always)]
    #[must_use]
    pub fn db4(&mut self) -> Db4W<Tmdata10Spec> {
        Db4W::new(self, 0)
    }
    #[doc = "Bits 8:15 - Data byte 5"]
    #[inline(always)]
    #[must_use]
    pub fn db5(&mut self) -> Db5W<Tmdata10Spec> {
        Db5W::new(self, 8)
    }
    #[doc = "Bits 16:23 - Data byte 6"]
    #[inline(always)]
    #[must_use]
    pub fn db6(&mut self) -> Db6W<Tmdata10Spec> {
        Db6W::new(self, 16)
    }
    #[doc = "Bits 24:31 - Data byte 7"]
    #[inline(always)]
    #[must_use]
    pub fn db7(&mut self) -> Db7W<Tmdata10Spec> {
        Db7W::new(self, 24)
    }
}
#[doc = "Transmit mailbox data1 register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`tmdata10::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`tmdata10::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Tmdata10Spec;
impl crate::RegisterSpec for Tmdata10Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`tmdata10::R`](R) reader structure"]
impl crate::Readable for Tmdata10Spec {}
#[doc = "`write(|w| ..)` method takes [`tmdata10::W`](W) writer structure"]
impl crate::Writable for Tmdata10Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets TMDATA10 to value 0"]
impl crate::Resettable for Tmdata10Spec {
    const RESET_VALUE: u32 = 0;
}
