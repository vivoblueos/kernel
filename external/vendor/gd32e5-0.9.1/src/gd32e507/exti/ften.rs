#[doc = "Register `FTEN` reader"]
pub type R = crate::R<FtenSpec>;
#[doc = "Register `FTEN` writer"]
pub type W = crate::W<FtenSpec>;
#[doc = "Falling edge trigger enable of line 0\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Ften0 {
    #[doc = "0: Falling edge trigger is disabled"]
    Disabled = 0,
    #[doc = "1: Falling edge trigger is enabled"]
    Enabled = 1,
}
impl From<Ften0> for bool {
    #[inline(always)]
    fn from(variant: Ften0) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `FTEN0` reader - Falling edge trigger enable of line 0"]
pub type Ften0R = crate::BitReader<Ften0>;
impl Ften0R {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Ften0 {
        match self.bits {
            false => Ften0::Disabled,
            true => Ften0::Enabled,
        }
    }
    #[doc = "Falling edge trigger is disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Ften0::Disabled
    }
    #[doc = "Falling edge trigger is enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Ften0::Enabled
    }
}
#[doc = "Field `FTEN0` writer - Falling edge trigger enable of line 0"]
pub type Ften0W<'a, REG> = crate::BitWriter<'a, REG, Ften0>;
impl<'a, REG> Ften0W<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Falling edge trigger is disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Ften0::Disabled)
    }
    #[doc = "Falling edge trigger is enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Ften0::Enabled)
    }
}
#[doc = "Field `FTEN1` reader - Falling edge trigger enable of line 1"]
pub use Ften0R as Ften1R;
#[doc = "Field `FTEN2` reader - Falling edge trigger enable of line 2"]
pub use Ften0R as Ften2R;
#[doc = "Field `FTEN3` reader - Falling edge trigger enable of line 3"]
pub use Ften0R as Ften3R;
#[doc = "Field `FTEN4` reader - Falling edge trigger enable of line 4"]
pub use Ften0R as Ften4R;
#[doc = "Field `FTEN5` reader - Falling edge trigger enable of line 5"]
pub use Ften0R as Ften5R;
#[doc = "Field `FTEN6` reader - Falling edge trigger enable of line 6"]
pub use Ften0R as Ften6R;
#[doc = "Field `FTEN7` reader - Falling edge trigger enable of line 7"]
pub use Ften0R as Ften7R;
#[doc = "Field `FTEN8` reader - Falling edge trigger enable of line 8"]
pub use Ften0R as Ften8R;
#[doc = "Field `FTEN9` reader - Falling edge trigger enable of line 9"]
pub use Ften0R as Ften9R;
#[doc = "Field `FTEN10` reader - Falling edge trigger enable of line 10"]
pub use Ften0R as Ften10R;
#[doc = "Field `FTEN11` reader - Falling edge trigger enable of line 11"]
pub use Ften0R as Ften11R;
#[doc = "Field `FTEN12` reader - Falling edge trigger enable of line 12"]
pub use Ften0R as Ften12R;
#[doc = "Field `FTEN13` reader - Falling edge trigger enable of line 13"]
pub use Ften0R as Ften13R;
#[doc = "Field `FTEN14` reader - Falling edge trigger enable of line 14"]
pub use Ften0R as Ften14R;
#[doc = "Field `FTEN15` reader - Falling edge trigger enable of line 15"]
pub use Ften0R as Ften15R;
#[doc = "Field `FTEN16` reader - Falling edge trigger enable of line 16"]
pub use Ften0R as Ften16R;
#[doc = "Field `FTEN17` reader - Falling edge trigger enable of line 17"]
pub use Ften0R as Ften17R;
#[doc = "Field `FTEN18` reader - Falling edge trigger enable of line 18"]
pub use Ften0R as Ften18R;
#[doc = "Field `FTEN19` reader - Falling edge trigger enable of line 19"]
pub use Ften0R as Ften19R;
#[doc = "Field `FTEN20` reader - Falling edge trigger enable of line 20"]
pub use Ften0R as Ften20R;
#[doc = "Field `FTEN21` reader - Falling edge trigger enable of line 21"]
pub use Ften0R as Ften21R;
#[doc = "Field `FTEN1` writer - Falling edge trigger enable of line 1"]
pub use Ften0W as Ften1W;
#[doc = "Field `FTEN2` writer - Falling edge trigger enable of line 2"]
pub use Ften0W as Ften2W;
#[doc = "Field `FTEN3` writer - Falling edge trigger enable of line 3"]
pub use Ften0W as Ften3W;
#[doc = "Field `FTEN4` writer - Falling edge trigger enable of line 4"]
pub use Ften0W as Ften4W;
#[doc = "Field `FTEN5` writer - Falling edge trigger enable of line 5"]
pub use Ften0W as Ften5W;
#[doc = "Field `FTEN6` writer - Falling edge trigger enable of line 6"]
pub use Ften0W as Ften6W;
#[doc = "Field `FTEN7` writer - Falling edge trigger enable of line 7"]
pub use Ften0W as Ften7W;
#[doc = "Field `FTEN8` writer - Falling edge trigger enable of line 8"]
pub use Ften0W as Ften8W;
#[doc = "Field `FTEN9` writer - Falling edge trigger enable of line 9"]
pub use Ften0W as Ften9W;
#[doc = "Field `FTEN10` writer - Falling edge trigger enable of line 10"]
pub use Ften0W as Ften10W;
#[doc = "Field `FTEN11` writer - Falling edge trigger enable of line 11"]
pub use Ften0W as Ften11W;
#[doc = "Field `FTEN12` writer - Falling edge trigger enable of line 12"]
pub use Ften0W as Ften12W;
#[doc = "Field `FTEN13` writer - Falling edge trigger enable of line 13"]
pub use Ften0W as Ften13W;
#[doc = "Field `FTEN14` writer - Falling edge trigger enable of line 14"]
pub use Ften0W as Ften14W;
#[doc = "Field `FTEN15` writer - Falling edge trigger enable of line 15"]
pub use Ften0W as Ften15W;
#[doc = "Field `FTEN16` writer - Falling edge trigger enable of line 16"]
pub use Ften0W as Ften16W;
#[doc = "Field `FTEN17` writer - Falling edge trigger enable of line 17"]
pub use Ften0W as Ften17W;
#[doc = "Field `FTEN18` writer - Falling edge trigger enable of line 18"]
pub use Ften0W as Ften18W;
#[doc = "Field `FTEN19` writer - Falling edge trigger enable of line 19"]
pub use Ften0W as Ften19W;
#[doc = "Field `FTEN20` writer - Falling edge trigger enable of line 20"]
pub use Ften0W as Ften20W;
#[doc = "Field `FTEN21` writer - Falling edge trigger enable of line 21"]
pub use Ften0W as Ften21W;
impl R {
    #[doc = "Bit 0 - Falling edge trigger enable of line 0"]
    #[inline(always)]
    pub fn ften0(&self) -> Ften0R {
        Ften0R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Falling edge trigger enable of line 1"]
    #[inline(always)]
    pub fn ften1(&self) -> Ften1R {
        Ften1R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Falling edge trigger enable of line 2"]
    #[inline(always)]
    pub fn ften2(&self) -> Ften2R {
        Ften2R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Falling edge trigger enable of line 3"]
    #[inline(always)]
    pub fn ften3(&self) -> Ften3R {
        Ften3R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Falling edge trigger enable of line 4"]
    #[inline(always)]
    pub fn ften4(&self) -> Ften4R {
        Ften4R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Falling edge trigger enable of line 5"]
    #[inline(always)]
    pub fn ften5(&self) -> Ften5R {
        Ften5R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Falling edge trigger enable of line 6"]
    #[inline(always)]
    pub fn ften6(&self) -> Ften6R {
        Ften6R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Falling edge trigger enable of line 7"]
    #[inline(always)]
    pub fn ften7(&self) -> Ften7R {
        Ften7R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Falling edge trigger enable of line 8"]
    #[inline(always)]
    pub fn ften8(&self) -> Ften8R {
        Ften8R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Falling edge trigger enable of line 9"]
    #[inline(always)]
    pub fn ften9(&self) -> Ften9R {
        Ften9R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Falling edge trigger enable of line 10"]
    #[inline(always)]
    pub fn ften10(&self) -> Ften10R {
        Ften10R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Falling edge trigger enable of line 11"]
    #[inline(always)]
    pub fn ften11(&self) -> Ften11R {
        Ften11R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Falling edge trigger enable of line 12"]
    #[inline(always)]
    pub fn ften12(&self) -> Ften12R {
        Ften12R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Falling edge trigger enable of line 13"]
    #[inline(always)]
    pub fn ften13(&self) -> Ften13R {
        Ften13R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Falling edge trigger enable of line 14"]
    #[inline(always)]
    pub fn ften14(&self) -> Ften14R {
        Ften14R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Falling edge trigger enable of line 15"]
    #[inline(always)]
    pub fn ften15(&self) -> Ften15R {
        Ften15R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - Falling edge trigger enable of line 16"]
    #[inline(always)]
    pub fn ften16(&self) -> Ften16R {
        Ften16R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - Falling edge trigger enable of line 17"]
    #[inline(always)]
    pub fn ften17(&self) -> Ften17R {
        Ften17R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - Falling edge trigger enable of line 18"]
    #[inline(always)]
    pub fn ften18(&self) -> Ften18R {
        Ften18R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - Falling edge trigger enable of line 19"]
    #[inline(always)]
    pub fn ften19(&self) -> Ften19R {
        Ften19R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - Falling edge trigger enable of line 20"]
    #[inline(always)]
    pub fn ften20(&self) -> Ften20R {
        Ften20R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - Falling edge trigger enable of line 21"]
    #[inline(always)]
    pub fn ften21(&self) -> Ften21R {
        Ften21R::new(((self.bits >> 21) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Falling edge trigger enable of line 0"]
    #[inline(always)]
    #[must_use]
    pub fn ften0(&mut self) -> Ften0W<FtenSpec> {
        Ften0W::new(self, 0)
    }
    #[doc = "Bit 1 - Falling edge trigger enable of line 1"]
    #[inline(always)]
    #[must_use]
    pub fn ften1(&mut self) -> Ften1W<FtenSpec> {
        Ften1W::new(self, 1)
    }
    #[doc = "Bit 2 - Falling edge trigger enable of line 2"]
    #[inline(always)]
    #[must_use]
    pub fn ften2(&mut self) -> Ften2W<FtenSpec> {
        Ften2W::new(self, 2)
    }
    #[doc = "Bit 3 - Falling edge trigger enable of line 3"]
    #[inline(always)]
    #[must_use]
    pub fn ften3(&mut self) -> Ften3W<FtenSpec> {
        Ften3W::new(self, 3)
    }
    #[doc = "Bit 4 - Falling edge trigger enable of line 4"]
    #[inline(always)]
    #[must_use]
    pub fn ften4(&mut self) -> Ften4W<FtenSpec> {
        Ften4W::new(self, 4)
    }
    #[doc = "Bit 5 - Falling edge trigger enable of line 5"]
    #[inline(always)]
    #[must_use]
    pub fn ften5(&mut self) -> Ften5W<FtenSpec> {
        Ften5W::new(self, 5)
    }
    #[doc = "Bit 6 - Falling edge trigger enable of line 6"]
    #[inline(always)]
    #[must_use]
    pub fn ften6(&mut self) -> Ften6W<FtenSpec> {
        Ften6W::new(self, 6)
    }
    #[doc = "Bit 7 - Falling edge trigger enable of line 7"]
    #[inline(always)]
    #[must_use]
    pub fn ften7(&mut self) -> Ften7W<FtenSpec> {
        Ften7W::new(self, 7)
    }
    #[doc = "Bit 8 - Falling edge trigger enable of line 8"]
    #[inline(always)]
    #[must_use]
    pub fn ften8(&mut self) -> Ften8W<FtenSpec> {
        Ften8W::new(self, 8)
    }
    #[doc = "Bit 9 - Falling edge trigger enable of line 9"]
    #[inline(always)]
    #[must_use]
    pub fn ften9(&mut self) -> Ften9W<FtenSpec> {
        Ften9W::new(self, 9)
    }
    #[doc = "Bit 10 - Falling edge trigger enable of line 10"]
    #[inline(always)]
    #[must_use]
    pub fn ften10(&mut self) -> Ften10W<FtenSpec> {
        Ften10W::new(self, 10)
    }
    #[doc = "Bit 11 - Falling edge trigger enable of line 11"]
    #[inline(always)]
    #[must_use]
    pub fn ften11(&mut self) -> Ften11W<FtenSpec> {
        Ften11W::new(self, 11)
    }
    #[doc = "Bit 12 - Falling edge trigger enable of line 12"]
    #[inline(always)]
    #[must_use]
    pub fn ften12(&mut self) -> Ften12W<FtenSpec> {
        Ften12W::new(self, 12)
    }
    #[doc = "Bit 13 - Falling edge trigger enable of line 13"]
    #[inline(always)]
    #[must_use]
    pub fn ften13(&mut self) -> Ften13W<FtenSpec> {
        Ften13W::new(self, 13)
    }
    #[doc = "Bit 14 - Falling edge trigger enable of line 14"]
    #[inline(always)]
    #[must_use]
    pub fn ften14(&mut self) -> Ften14W<FtenSpec> {
        Ften14W::new(self, 14)
    }
    #[doc = "Bit 15 - Falling edge trigger enable of line 15"]
    #[inline(always)]
    #[must_use]
    pub fn ften15(&mut self) -> Ften15W<FtenSpec> {
        Ften15W::new(self, 15)
    }
    #[doc = "Bit 16 - Falling edge trigger enable of line 16"]
    #[inline(always)]
    #[must_use]
    pub fn ften16(&mut self) -> Ften16W<FtenSpec> {
        Ften16W::new(self, 16)
    }
    #[doc = "Bit 17 - Falling edge trigger enable of line 17"]
    #[inline(always)]
    #[must_use]
    pub fn ften17(&mut self) -> Ften17W<FtenSpec> {
        Ften17W::new(self, 17)
    }
    #[doc = "Bit 18 - Falling edge trigger enable of line 18"]
    #[inline(always)]
    #[must_use]
    pub fn ften18(&mut self) -> Ften18W<FtenSpec> {
        Ften18W::new(self, 18)
    }
    #[doc = "Bit 19 - Falling edge trigger enable of line 19"]
    #[inline(always)]
    #[must_use]
    pub fn ften19(&mut self) -> Ften19W<FtenSpec> {
        Ften19W::new(self, 19)
    }
    #[doc = "Bit 20 - Falling edge trigger enable of line 20"]
    #[inline(always)]
    #[must_use]
    pub fn ften20(&mut self) -> Ften20W<FtenSpec> {
        Ften20W::new(self, 20)
    }
    #[doc = "Bit 21 - Falling edge trigger enable of line 21"]
    #[inline(always)]
    #[must_use]
    pub fn ften21(&mut self) -> Ften21W<FtenSpec> {
        Ften21W::new(self, 21)
    }
}
#[doc = "Falling Egde Trigger Enable register (EXTI_FTEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ften::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ften::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct FtenSpec;
impl crate::RegisterSpec for FtenSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ften::R`](R) reader structure"]
impl crate::Readable for FtenSpec {}
#[doc = "`write(|w| ..)` method takes [`ften::W`](W) writer structure"]
impl crate::Writable for FtenSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets FTEN to value 0"]
impl crate::Resettable for FtenSpec {
    const RESET_VALUE: u32 = 0;
}
