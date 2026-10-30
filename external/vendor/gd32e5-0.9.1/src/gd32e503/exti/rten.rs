#[doc = "Register `RTEN` reader"]
pub type R = crate::R<RtenSpec>;
#[doc = "Register `RTEN` writer"]
pub type W = crate::W<RtenSpec>;
#[doc = "Rising edge trigger enable of line 0\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Rten0 {
    #[doc = "0: Rising edge trigger is disabled"]
    Disabled = 0,
    #[doc = "1: Rising edge trigger is enabled"]
    Enabled = 1,
}
impl From<Rten0> for bool {
    #[inline(always)]
    fn from(variant: Rten0) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `RTEN0` reader - Rising edge trigger enable of line 0"]
pub type Rten0R = crate::BitReader<Rten0>;
impl Rten0R {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Rten0 {
        match self.bits {
            false => Rten0::Disabled,
            true => Rten0::Enabled,
        }
    }
    #[doc = "Rising edge trigger is disabled"]
    #[inline(always)]
    pub fn is_disabled(&self) -> bool {
        *self == Rten0::Disabled
    }
    #[doc = "Rising edge trigger is enabled"]
    #[inline(always)]
    pub fn is_enabled(&self) -> bool {
        *self == Rten0::Enabled
    }
}
#[doc = "Field `RTEN0` writer - Rising edge trigger enable of line 0"]
pub type Rten0W<'a, REG> = crate::BitWriter<'a, REG, Rten0>;
impl<'a, REG> Rten0W<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Rising edge trigger is disabled"]
    #[inline(always)]
    pub fn disabled(self) -> &'a mut crate::W<REG> {
        self.variant(Rten0::Disabled)
    }
    #[doc = "Rising edge trigger is enabled"]
    #[inline(always)]
    pub fn enabled(self) -> &'a mut crate::W<REG> {
        self.variant(Rten0::Enabled)
    }
}
#[doc = "Field `RTEN1` reader - Rising edge trigger enable of line 1"]
pub use Rten0R as Rten1R;
#[doc = "Field `RTEN2` reader - Rising edge trigger enable of line 2"]
pub use Rten0R as Rten2R;
#[doc = "Field `RTEN3` reader - Rising edge trigger enable of line 3"]
pub use Rten0R as Rten3R;
#[doc = "Field `RTEN4` reader - Rising edge trigger enable of line 4"]
pub use Rten0R as Rten4R;
#[doc = "Field `RTEN5` reader - Rising edge trigger enable of line 5"]
pub use Rten0R as Rten5R;
#[doc = "Field `RTEN6` reader - Rising edge trigger enable of line 6"]
pub use Rten0R as Rten6R;
#[doc = "Field `RTEN7` reader - Rising edge trigger enable of line 7"]
pub use Rten0R as Rten7R;
#[doc = "Field `RTEN8` reader - Rising edge trigger enable of line 8"]
pub use Rten0R as Rten8R;
#[doc = "Field `RTEN9` reader - Rising edge trigger enable of line 9"]
pub use Rten0R as Rten9R;
#[doc = "Field `RTEN10` reader - Rising edge trigger enable of line 10"]
pub use Rten0R as Rten10R;
#[doc = "Field `RTEN11` reader - Rising edge trigger enable of line 11"]
pub use Rten0R as Rten11R;
#[doc = "Field `RTEN12` reader - Rising edge trigger enable of line 12"]
pub use Rten0R as Rten12R;
#[doc = "Field `RTEN13` reader - Rising edge trigger enable of line 13"]
pub use Rten0R as Rten13R;
#[doc = "Field `RTEN14` reader - Rising edge trigger enable of line 14"]
pub use Rten0R as Rten14R;
#[doc = "Field `RTEN15` reader - Rising edge trigger enable of line 15"]
pub use Rten0R as Rten15R;
#[doc = "Field `RTEN16` reader - Rising edge trigger enable of line 16"]
pub use Rten0R as Rten16R;
#[doc = "Field `RTEN17` reader - Rising edge trigger enable of line 17"]
pub use Rten0R as Rten17R;
#[doc = "Field `RTEN18` reader - Rising edge trigger enable of line 18"]
pub use Rten0R as Rten18R;
#[doc = "Field `RTEN19` reader - Rising edge trigger enable of line 19"]
pub use Rten0R as Rten19R;
#[doc = "Field `RTEN20` reader - Rising edge trigger enable of line 20"]
pub use Rten0R as Rten20R;
#[doc = "Field `RTEN21` reader - Rising edge trigger enable of line 21"]
pub use Rten0R as Rten21R;
#[doc = "Field `RTEN1` writer - Rising edge trigger enable of line 1"]
pub use Rten0W as Rten1W;
#[doc = "Field `RTEN2` writer - Rising edge trigger enable of line 2"]
pub use Rten0W as Rten2W;
#[doc = "Field `RTEN3` writer - Rising edge trigger enable of line 3"]
pub use Rten0W as Rten3W;
#[doc = "Field `RTEN4` writer - Rising edge trigger enable of line 4"]
pub use Rten0W as Rten4W;
#[doc = "Field `RTEN5` writer - Rising edge trigger enable of line 5"]
pub use Rten0W as Rten5W;
#[doc = "Field `RTEN6` writer - Rising edge trigger enable of line 6"]
pub use Rten0W as Rten6W;
#[doc = "Field `RTEN7` writer - Rising edge trigger enable of line 7"]
pub use Rten0W as Rten7W;
#[doc = "Field `RTEN8` writer - Rising edge trigger enable of line 8"]
pub use Rten0W as Rten8W;
#[doc = "Field `RTEN9` writer - Rising edge trigger enable of line 9"]
pub use Rten0W as Rten9W;
#[doc = "Field `RTEN10` writer - Rising edge trigger enable of line 10"]
pub use Rten0W as Rten10W;
#[doc = "Field `RTEN11` writer - Rising edge trigger enable of line 11"]
pub use Rten0W as Rten11W;
#[doc = "Field `RTEN12` writer - Rising edge trigger enable of line 12"]
pub use Rten0W as Rten12W;
#[doc = "Field `RTEN13` writer - Rising edge trigger enable of line 13"]
pub use Rten0W as Rten13W;
#[doc = "Field `RTEN14` writer - Rising edge trigger enable of line 14"]
pub use Rten0W as Rten14W;
#[doc = "Field `RTEN15` writer - Rising edge trigger enable of line 15"]
pub use Rten0W as Rten15W;
#[doc = "Field `RTEN16` writer - Rising edge trigger enable of line 16"]
pub use Rten0W as Rten16W;
#[doc = "Field `RTEN17` writer - Rising edge trigger enable of line 17"]
pub use Rten0W as Rten17W;
#[doc = "Field `RTEN18` writer - Rising edge trigger enable of line 18"]
pub use Rten0W as Rten18W;
#[doc = "Field `RTEN19` writer - Rising edge trigger enable of line 19"]
pub use Rten0W as Rten19W;
#[doc = "Field `RTEN20` writer - Rising edge trigger enable of line 20"]
pub use Rten0W as Rten20W;
#[doc = "Field `RTEN21` writer - Rising edge trigger enable of line 21"]
pub use Rten0W as Rten21W;
impl R {
    #[doc = "Bit 0 - Rising edge trigger enable of line 0"]
    #[inline(always)]
    pub fn rten0(&self) -> Rten0R {
        Rten0R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Rising edge trigger enable of line 1"]
    #[inline(always)]
    pub fn rten1(&self) -> Rten1R {
        Rten1R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Rising edge trigger enable of line 2"]
    #[inline(always)]
    pub fn rten2(&self) -> Rten2R {
        Rten2R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Rising edge trigger enable of line 3"]
    #[inline(always)]
    pub fn rten3(&self) -> Rten3R {
        Rten3R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Rising edge trigger enable of line 4"]
    #[inline(always)]
    pub fn rten4(&self) -> Rten4R {
        Rten4R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Rising edge trigger enable of line 5"]
    #[inline(always)]
    pub fn rten5(&self) -> Rten5R {
        Rten5R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Rising edge trigger enable of line 6"]
    #[inline(always)]
    pub fn rten6(&self) -> Rten6R {
        Rten6R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Rising edge trigger enable of line 7"]
    #[inline(always)]
    pub fn rten7(&self) -> Rten7R {
        Rten7R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Rising edge trigger enable of line 8"]
    #[inline(always)]
    pub fn rten8(&self) -> Rten8R {
        Rten8R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Rising edge trigger enable of line 9"]
    #[inline(always)]
    pub fn rten9(&self) -> Rten9R {
        Rten9R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Rising edge trigger enable of line 10"]
    #[inline(always)]
    pub fn rten10(&self) -> Rten10R {
        Rten10R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Rising edge trigger enable of line 11"]
    #[inline(always)]
    pub fn rten11(&self) -> Rten11R {
        Rten11R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Rising edge trigger enable of line 12"]
    #[inline(always)]
    pub fn rten12(&self) -> Rten12R {
        Rten12R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Rising edge trigger enable of line 13"]
    #[inline(always)]
    pub fn rten13(&self) -> Rten13R {
        Rten13R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Rising edge trigger enable of line 14"]
    #[inline(always)]
    pub fn rten14(&self) -> Rten14R {
        Rten14R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Rising edge trigger enable of line 15"]
    #[inline(always)]
    pub fn rten15(&self) -> Rten15R {
        Rten15R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - Rising edge trigger enable of line 16"]
    #[inline(always)]
    pub fn rten16(&self) -> Rten16R {
        Rten16R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - Rising edge trigger enable of line 17"]
    #[inline(always)]
    pub fn rten17(&self) -> Rten17R {
        Rten17R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - Rising edge trigger enable of line 18"]
    #[inline(always)]
    pub fn rten18(&self) -> Rten18R {
        Rten18R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - Rising edge trigger enable of line 19"]
    #[inline(always)]
    pub fn rten19(&self) -> Rten19R {
        Rten19R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - Rising edge trigger enable of line 20"]
    #[inline(always)]
    pub fn rten20(&self) -> Rten20R {
        Rten20R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - Rising edge trigger enable of line 21"]
    #[inline(always)]
    pub fn rten21(&self) -> Rten21R {
        Rten21R::new(((self.bits >> 21) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Rising edge trigger enable of line 0"]
    #[inline(always)]
    #[must_use]
    pub fn rten0(&mut self) -> Rten0W<RtenSpec> {
        Rten0W::new(self, 0)
    }
    #[doc = "Bit 1 - Rising edge trigger enable of line 1"]
    #[inline(always)]
    #[must_use]
    pub fn rten1(&mut self) -> Rten1W<RtenSpec> {
        Rten1W::new(self, 1)
    }
    #[doc = "Bit 2 - Rising edge trigger enable of line 2"]
    #[inline(always)]
    #[must_use]
    pub fn rten2(&mut self) -> Rten2W<RtenSpec> {
        Rten2W::new(self, 2)
    }
    #[doc = "Bit 3 - Rising edge trigger enable of line 3"]
    #[inline(always)]
    #[must_use]
    pub fn rten3(&mut self) -> Rten3W<RtenSpec> {
        Rten3W::new(self, 3)
    }
    #[doc = "Bit 4 - Rising edge trigger enable of line 4"]
    #[inline(always)]
    #[must_use]
    pub fn rten4(&mut self) -> Rten4W<RtenSpec> {
        Rten4W::new(self, 4)
    }
    #[doc = "Bit 5 - Rising edge trigger enable of line 5"]
    #[inline(always)]
    #[must_use]
    pub fn rten5(&mut self) -> Rten5W<RtenSpec> {
        Rten5W::new(self, 5)
    }
    #[doc = "Bit 6 - Rising edge trigger enable of line 6"]
    #[inline(always)]
    #[must_use]
    pub fn rten6(&mut self) -> Rten6W<RtenSpec> {
        Rten6W::new(self, 6)
    }
    #[doc = "Bit 7 - Rising edge trigger enable of line 7"]
    #[inline(always)]
    #[must_use]
    pub fn rten7(&mut self) -> Rten7W<RtenSpec> {
        Rten7W::new(self, 7)
    }
    #[doc = "Bit 8 - Rising edge trigger enable of line 8"]
    #[inline(always)]
    #[must_use]
    pub fn rten8(&mut self) -> Rten8W<RtenSpec> {
        Rten8W::new(self, 8)
    }
    #[doc = "Bit 9 - Rising edge trigger enable of line 9"]
    #[inline(always)]
    #[must_use]
    pub fn rten9(&mut self) -> Rten9W<RtenSpec> {
        Rten9W::new(self, 9)
    }
    #[doc = "Bit 10 - Rising edge trigger enable of line 10"]
    #[inline(always)]
    #[must_use]
    pub fn rten10(&mut self) -> Rten10W<RtenSpec> {
        Rten10W::new(self, 10)
    }
    #[doc = "Bit 11 - Rising edge trigger enable of line 11"]
    #[inline(always)]
    #[must_use]
    pub fn rten11(&mut self) -> Rten11W<RtenSpec> {
        Rten11W::new(self, 11)
    }
    #[doc = "Bit 12 - Rising edge trigger enable of line 12"]
    #[inline(always)]
    #[must_use]
    pub fn rten12(&mut self) -> Rten12W<RtenSpec> {
        Rten12W::new(self, 12)
    }
    #[doc = "Bit 13 - Rising edge trigger enable of line 13"]
    #[inline(always)]
    #[must_use]
    pub fn rten13(&mut self) -> Rten13W<RtenSpec> {
        Rten13W::new(self, 13)
    }
    #[doc = "Bit 14 - Rising edge trigger enable of line 14"]
    #[inline(always)]
    #[must_use]
    pub fn rten14(&mut self) -> Rten14W<RtenSpec> {
        Rten14W::new(self, 14)
    }
    #[doc = "Bit 15 - Rising edge trigger enable of line 15"]
    #[inline(always)]
    #[must_use]
    pub fn rten15(&mut self) -> Rten15W<RtenSpec> {
        Rten15W::new(self, 15)
    }
    #[doc = "Bit 16 - Rising edge trigger enable of line 16"]
    #[inline(always)]
    #[must_use]
    pub fn rten16(&mut self) -> Rten16W<RtenSpec> {
        Rten16W::new(self, 16)
    }
    #[doc = "Bit 17 - Rising edge trigger enable of line 17"]
    #[inline(always)]
    #[must_use]
    pub fn rten17(&mut self) -> Rten17W<RtenSpec> {
        Rten17W::new(self, 17)
    }
    #[doc = "Bit 18 - Rising edge trigger enable of line 18"]
    #[inline(always)]
    #[must_use]
    pub fn rten18(&mut self) -> Rten18W<RtenSpec> {
        Rten18W::new(self, 18)
    }
    #[doc = "Bit 19 - Rising edge trigger enable of line 19"]
    #[inline(always)]
    #[must_use]
    pub fn rten19(&mut self) -> Rten19W<RtenSpec> {
        Rten19W::new(self, 19)
    }
    #[doc = "Bit 20 - Rising edge trigger enable of line 20"]
    #[inline(always)]
    #[must_use]
    pub fn rten20(&mut self) -> Rten20W<RtenSpec> {
        Rten20W::new(self, 20)
    }
    #[doc = "Bit 21 - Rising edge trigger enable of line 21"]
    #[inline(always)]
    #[must_use]
    pub fn rten21(&mut self) -> Rten21W<RtenSpec> {
        Rten21W::new(self, 21)
    }
}
#[doc = "Rising Edge Trigger Enable register (EXTI_RTEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`rten::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`rten::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct RtenSpec;
impl crate::RegisterSpec for RtenSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`rten::R`](R) reader structure"]
impl crate::Readable for RtenSpec {}
#[doc = "`write(|w| ..)` method takes [`rten::W`](W) writer structure"]
impl crate::Writable for RtenSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets RTEN to value 0"]
impl crate::Resettable for RtenSpec {
    const RESET_VALUE: u32 = 0;
}
