#[doc = "Register `INTEN` reader"]
pub type R = crate::R<IntenSpec>;
#[doc = "Register `INTEN` writer"]
pub type W = crate::W<IntenSpec>;
#[doc = "Enable Interrupt on line 0\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Inten0 {
    #[doc = "0: Interrupt from line is disabled"]
    Masked = 0,
    #[doc = "1: Interrupt from line is enabled"]
    Unmasked = 1,
}
impl From<Inten0> for bool {
    #[inline(always)]
    fn from(variant: Inten0) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `INTEN0` reader - Enable Interrupt on line 0"]
pub type Inten0R = crate::BitReader<Inten0>;
impl Inten0R {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Inten0 {
        match self.bits {
            false => Inten0::Masked,
            true => Inten0::Unmasked,
        }
    }
    #[doc = "Interrupt from line is disabled"]
    #[inline(always)]
    pub fn is_masked(&self) -> bool {
        *self == Inten0::Masked
    }
    #[doc = "Interrupt from line is enabled"]
    #[inline(always)]
    pub fn is_unmasked(&self) -> bool {
        *self == Inten0::Unmasked
    }
}
#[doc = "Field `INTEN0` writer - Enable Interrupt on line 0"]
pub type Inten0W<'a, REG> = crate::BitWriter<'a, REG, Inten0>;
impl<'a, REG> Inten0W<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Interrupt from line is disabled"]
    #[inline(always)]
    pub fn masked(self) -> &'a mut crate::W<REG> {
        self.variant(Inten0::Masked)
    }
    #[doc = "Interrupt from line is enabled"]
    #[inline(always)]
    pub fn unmasked(self) -> &'a mut crate::W<REG> {
        self.variant(Inten0::Unmasked)
    }
}
#[doc = "Field `INTEN1` reader - Enable Interrupt on line 1"]
pub use Inten0R as Inten1R;
#[doc = "Field `INTEN2` reader - Enable Interrupt on line 2"]
pub use Inten0R as Inten2R;
#[doc = "Field `INTEN3` reader - Enable Interrupt on line 3"]
pub use Inten0R as Inten3R;
#[doc = "Field `INTEN4` reader - Enable Interrupt on line 4"]
pub use Inten0R as Inten4R;
#[doc = "Field `INTEN5` reader - Enable Interrupt on line 5"]
pub use Inten0R as Inten5R;
#[doc = "Field `INTEN6` reader - Enable Interrupt on line 6"]
pub use Inten0R as Inten6R;
#[doc = "Field `INTEN7` reader - Enable Interrupt on line 7"]
pub use Inten0R as Inten7R;
#[doc = "Field `INTEN8` reader - Enable Interrupt on line 8"]
pub use Inten0R as Inten8R;
#[doc = "Field `INTEN9` reader - Enable Interrupt on line 9"]
pub use Inten0R as Inten9R;
#[doc = "Field `INTEN10` reader - Enable Interrupt on line 10"]
pub use Inten0R as Inten10R;
#[doc = "Field `INTEN11` reader - Enable Interrupt on line 11"]
pub use Inten0R as Inten11R;
#[doc = "Field `INTEN12` reader - Enable Interrupt on line 12"]
pub use Inten0R as Inten12R;
#[doc = "Field `INTEN13` reader - Enable Interrupt on line 13"]
pub use Inten0R as Inten13R;
#[doc = "Field `INTEN14` reader - Enable Interrupt on line 14"]
pub use Inten0R as Inten14R;
#[doc = "Field `INTEN15` reader - Enable Interrupt on line 15"]
pub use Inten0R as Inten15R;
#[doc = "Field `INTEN16` reader - Enable Interrupt on line 16"]
pub use Inten0R as Inten16R;
#[doc = "Field `INTEN17` reader - Enable Interrupt on line 17"]
pub use Inten0R as Inten17R;
#[doc = "Field `INTEN18` reader - Enable Interrupt on line 18"]
pub use Inten0R as Inten18R;
#[doc = "Field `INTEN19` reader - Enable Interrupt on line 19"]
pub use Inten0R as Inten19R;
#[doc = "Field `INTEN20` reader - Enable Interrupt on line 20"]
pub use Inten0R as Inten20R;
#[doc = "Field `INTEN21` reader - Enable Interrupt on line 21"]
pub use Inten0R as Inten21R;
#[doc = "Field `INTEN1` writer - Enable Interrupt on line 1"]
pub use Inten0W as Inten1W;
#[doc = "Field `INTEN2` writer - Enable Interrupt on line 2"]
pub use Inten0W as Inten2W;
#[doc = "Field `INTEN3` writer - Enable Interrupt on line 3"]
pub use Inten0W as Inten3W;
#[doc = "Field `INTEN4` writer - Enable Interrupt on line 4"]
pub use Inten0W as Inten4W;
#[doc = "Field `INTEN5` writer - Enable Interrupt on line 5"]
pub use Inten0W as Inten5W;
#[doc = "Field `INTEN6` writer - Enable Interrupt on line 6"]
pub use Inten0W as Inten6W;
#[doc = "Field `INTEN7` writer - Enable Interrupt on line 7"]
pub use Inten0W as Inten7W;
#[doc = "Field `INTEN8` writer - Enable Interrupt on line 8"]
pub use Inten0W as Inten8W;
#[doc = "Field `INTEN9` writer - Enable Interrupt on line 9"]
pub use Inten0W as Inten9W;
#[doc = "Field `INTEN10` writer - Enable Interrupt on line 10"]
pub use Inten0W as Inten10W;
#[doc = "Field `INTEN11` writer - Enable Interrupt on line 11"]
pub use Inten0W as Inten11W;
#[doc = "Field `INTEN12` writer - Enable Interrupt on line 12"]
pub use Inten0W as Inten12W;
#[doc = "Field `INTEN13` writer - Enable Interrupt on line 13"]
pub use Inten0W as Inten13W;
#[doc = "Field `INTEN14` writer - Enable Interrupt on line 14"]
pub use Inten0W as Inten14W;
#[doc = "Field `INTEN15` writer - Enable Interrupt on line 15"]
pub use Inten0W as Inten15W;
#[doc = "Field `INTEN16` writer - Enable Interrupt on line 16"]
pub use Inten0W as Inten16W;
#[doc = "Field `INTEN17` writer - Enable Interrupt on line 17"]
pub use Inten0W as Inten17W;
#[doc = "Field `INTEN18` writer - Enable Interrupt on line 18"]
pub use Inten0W as Inten18W;
#[doc = "Field `INTEN19` writer - Enable Interrupt on line 19"]
pub use Inten0W as Inten19W;
#[doc = "Field `INTEN20` writer - Enable Interrupt on line 20"]
pub use Inten0W as Inten20W;
#[doc = "Field `INTEN21` writer - Enable Interrupt on line 21"]
pub use Inten0W as Inten21W;
impl R {
    #[doc = "Bit 0 - Enable Interrupt on line 0"]
    #[inline(always)]
    pub fn inten0(&self) -> Inten0R {
        Inten0R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Enable Interrupt on line 1"]
    #[inline(always)]
    pub fn inten1(&self) -> Inten1R {
        Inten1R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Enable Interrupt on line 2"]
    #[inline(always)]
    pub fn inten2(&self) -> Inten2R {
        Inten2R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Enable Interrupt on line 3"]
    #[inline(always)]
    pub fn inten3(&self) -> Inten3R {
        Inten3R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Enable Interrupt on line 4"]
    #[inline(always)]
    pub fn inten4(&self) -> Inten4R {
        Inten4R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Enable Interrupt on line 5"]
    #[inline(always)]
    pub fn inten5(&self) -> Inten5R {
        Inten5R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Enable Interrupt on line 6"]
    #[inline(always)]
    pub fn inten6(&self) -> Inten6R {
        Inten6R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Enable Interrupt on line 7"]
    #[inline(always)]
    pub fn inten7(&self) -> Inten7R {
        Inten7R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Enable Interrupt on line 8"]
    #[inline(always)]
    pub fn inten8(&self) -> Inten8R {
        Inten8R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Enable Interrupt on line 9"]
    #[inline(always)]
    pub fn inten9(&self) -> Inten9R {
        Inten9R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Enable Interrupt on line 10"]
    #[inline(always)]
    pub fn inten10(&self) -> Inten10R {
        Inten10R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Enable Interrupt on line 11"]
    #[inline(always)]
    pub fn inten11(&self) -> Inten11R {
        Inten11R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Enable Interrupt on line 12"]
    #[inline(always)]
    pub fn inten12(&self) -> Inten12R {
        Inten12R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Enable Interrupt on line 13"]
    #[inline(always)]
    pub fn inten13(&self) -> Inten13R {
        Inten13R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Enable Interrupt on line 14"]
    #[inline(always)]
    pub fn inten14(&self) -> Inten14R {
        Inten14R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Enable Interrupt on line 15"]
    #[inline(always)]
    pub fn inten15(&self) -> Inten15R {
        Inten15R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - Enable Interrupt on line 16"]
    #[inline(always)]
    pub fn inten16(&self) -> Inten16R {
        Inten16R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - Enable Interrupt on line 17"]
    #[inline(always)]
    pub fn inten17(&self) -> Inten17R {
        Inten17R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - Enable Interrupt on line 18"]
    #[inline(always)]
    pub fn inten18(&self) -> Inten18R {
        Inten18R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - Enable Interrupt on line 19"]
    #[inline(always)]
    pub fn inten19(&self) -> Inten19R {
        Inten19R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - Enable Interrupt on line 20"]
    #[inline(always)]
    pub fn inten20(&self) -> Inten20R {
        Inten20R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - Enable Interrupt on line 21"]
    #[inline(always)]
    pub fn inten21(&self) -> Inten21R {
        Inten21R::new(((self.bits >> 21) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Enable Interrupt on line 0"]
    #[inline(always)]
    #[must_use]
    pub fn inten0(&mut self) -> Inten0W<IntenSpec> {
        Inten0W::new(self, 0)
    }
    #[doc = "Bit 1 - Enable Interrupt on line 1"]
    #[inline(always)]
    #[must_use]
    pub fn inten1(&mut self) -> Inten1W<IntenSpec> {
        Inten1W::new(self, 1)
    }
    #[doc = "Bit 2 - Enable Interrupt on line 2"]
    #[inline(always)]
    #[must_use]
    pub fn inten2(&mut self) -> Inten2W<IntenSpec> {
        Inten2W::new(self, 2)
    }
    #[doc = "Bit 3 - Enable Interrupt on line 3"]
    #[inline(always)]
    #[must_use]
    pub fn inten3(&mut self) -> Inten3W<IntenSpec> {
        Inten3W::new(self, 3)
    }
    #[doc = "Bit 4 - Enable Interrupt on line 4"]
    #[inline(always)]
    #[must_use]
    pub fn inten4(&mut self) -> Inten4W<IntenSpec> {
        Inten4W::new(self, 4)
    }
    #[doc = "Bit 5 - Enable Interrupt on line 5"]
    #[inline(always)]
    #[must_use]
    pub fn inten5(&mut self) -> Inten5W<IntenSpec> {
        Inten5W::new(self, 5)
    }
    #[doc = "Bit 6 - Enable Interrupt on line 6"]
    #[inline(always)]
    #[must_use]
    pub fn inten6(&mut self) -> Inten6W<IntenSpec> {
        Inten6W::new(self, 6)
    }
    #[doc = "Bit 7 - Enable Interrupt on line 7"]
    #[inline(always)]
    #[must_use]
    pub fn inten7(&mut self) -> Inten7W<IntenSpec> {
        Inten7W::new(self, 7)
    }
    #[doc = "Bit 8 - Enable Interrupt on line 8"]
    #[inline(always)]
    #[must_use]
    pub fn inten8(&mut self) -> Inten8W<IntenSpec> {
        Inten8W::new(self, 8)
    }
    #[doc = "Bit 9 - Enable Interrupt on line 9"]
    #[inline(always)]
    #[must_use]
    pub fn inten9(&mut self) -> Inten9W<IntenSpec> {
        Inten9W::new(self, 9)
    }
    #[doc = "Bit 10 - Enable Interrupt on line 10"]
    #[inline(always)]
    #[must_use]
    pub fn inten10(&mut self) -> Inten10W<IntenSpec> {
        Inten10W::new(self, 10)
    }
    #[doc = "Bit 11 - Enable Interrupt on line 11"]
    #[inline(always)]
    #[must_use]
    pub fn inten11(&mut self) -> Inten11W<IntenSpec> {
        Inten11W::new(self, 11)
    }
    #[doc = "Bit 12 - Enable Interrupt on line 12"]
    #[inline(always)]
    #[must_use]
    pub fn inten12(&mut self) -> Inten12W<IntenSpec> {
        Inten12W::new(self, 12)
    }
    #[doc = "Bit 13 - Enable Interrupt on line 13"]
    #[inline(always)]
    #[must_use]
    pub fn inten13(&mut self) -> Inten13W<IntenSpec> {
        Inten13W::new(self, 13)
    }
    #[doc = "Bit 14 - Enable Interrupt on line 14"]
    #[inline(always)]
    #[must_use]
    pub fn inten14(&mut self) -> Inten14W<IntenSpec> {
        Inten14W::new(self, 14)
    }
    #[doc = "Bit 15 - Enable Interrupt on line 15"]
    #[inline(always)]
    #[must_use]
    pub fn inten15(&mut self) -> Inten15W<IntenSpec> {
        Inten15W::new(self, 15)
    }
    #[doc = "Bit 16 - Enable Interrupt on line 16"]
    #[inline(always)]
    #[must_use]
    pub fn inten16(&mut self) -> Inten16W<IntenSpec> {
        Inten16W::new(self, 16)
    }
    #[doc = "Bit 17 - Enable Interrupt on line 17"]
    #[inline(always)]
    #[must_use]
    pub fn inten17(&mut self) -> Inten17W<IntenSpec> {
        Inten17W::new(self, 17)
    }
    #[doc = "Bit 18 - Enable Interrupt on line 18"]
    #[inline(always)]
    #[must_use]
    pub fn inten18(&mut self) -> Inten18W<IntenSpec> {
        Inten18W::new(self, 18)
    }
    #[doc = "Bit 19 - Enable Interrupt on line 19"]
    #[inline(always)]
    #[must_use]
    pub fn inten19(&mut self) -> Inten19W<IntenSpec> {
        Inten19W::new(self, 19)
    }
    #[doc = "Bit 20 - Enable Interrupt on line 20"]
    #[inline(always)]
    #[must_use]
    pub fn inten20(&mut self) -> Inten20W<IntenSpec> {
        Inten20W::new(self, 20)
    }
    #[doc = "Bit 21 - Enable Interrupt on line 21"]
    #[inline(always)]
    #[must_use]
    pub fn inten21(&mut self) -> Inten21W<IntenSpec> {
        Inten21W::new(self, 21)
    }
}
#[doc = "Interrupt enable register (EXTI_INTEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`inten::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`inten::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IntenSpec;
impl crate::RegisterSpec for IntenSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`inten::R`](R) reader structure"]
impl crate::Readable for IntenSpec {}
#[doc = "`write(|w| ..)` method takes [`inten::W`](W) writer structure"]
impl crate::Writable for IntenSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets INTEN to value 0"]
impl crate::Resettable for IntenSpec {
    const RESET_VALUE: u32 = 0;
}
