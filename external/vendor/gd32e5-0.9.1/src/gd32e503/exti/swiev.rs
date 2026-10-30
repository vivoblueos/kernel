#[doc = "Register `SWIEV` reader"]
pub type R = crate::R<SwievSpec>;
#[doc = "Register `SWIEV` writer"]
pub type W = crate::W<SwievSpec>;
#[doc = "Interrupt/Event software trigger on line 0\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Swiev0w {
    #[doc = "1: Generates an interrupt request"]
    Pend = 1,
}
impl From<Swiev0w> for bool {
    #[inline(always)]
    fn from(variant: Swiev0w) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `SWIEV0` reader - Interrupt/Event software trigger on line 0"]
pub type Swiev0R = crate::BitReader<Swiev0w>;
impl Swiev0R {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Option<Swiev0w> {
        match self.bits {
            true => Some(Swiev0w::Pend),
            _ => None,
        }
    }
    #[doc = "Generates an interrupt request"]
    #[inline(always)]
    pub fn is_pend(&self) -> bool {
        *self == Swiev0w::Pend
    }
}
#[doc = "Field `SWIEV0` writer - Interrupt/Event software trigger on line 0"]
pub type Swiev0W<'a, REG> = crate::BitWriter<'a, REG, Swiev0w>;
impl<'a, REG> Swiev0W<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Generates an interrupt request"]
    #[inline(always)]
    pub fn pend(self) -> &'a mut crate::W<REG> {
        self.variant(Swiev0w::Pend)
    }
}
#[doc = "Field `SWIEV1` reader - Interrupt/Event software trigger on line 1"]
pub use Swiev0R as Swiev1R;
#[doc = "Field `SWIEV2` reader - Interrupt/Event software trigger on line 2"]
pub use Swiev0R as Swiev2R;
#[doc = "Field `SWIEV3` reader - Interrupt/Event software trigger on line 3"]
pub use Swiev0R as Swiev3R;
#[doc = "Field `SWIEV4` reader - Interrupt/Event software trigger on line 4"]
pub use Swiev0R as Swiev4R;
#[doc = "Field `SWIEV5` reader - Interrupt/Event software trigger on line 5"]
pub use Swiev0R as Swiev5R;
#[doc = "Field `SWIEV6` reader - Interrupt/Event software trigger on line 6"]
pub use Swiev0R as Swiev6R;
#[doc = "Field `SWIEV7` reader - Interrupt/Event software trigger on line 7"]
pub use Swiev0R as Swiev7R;
#[doc = "Field `SWIEV8` reader - Interrupt/Event software trigger on line 8"]
pub use Swiev0R as Swiev8R;
#[doc = "Field `SWIEV9` reader - Interrupt/Event software trigger on line 9"]
pub use Swiev0R as Swiev9R;
#[doc = "Field `SWIEV10` reader - Interrupt/Event software trigger on line 10"]
pub use Swiev0R as Swiev10R;
#[doc = "Field `SWIEV11` reader - Interrupt/Event software trigger on line 11"]
pub use Swiev0R as Swiev11R;
#[doc = "Field `SWIEV12` reader - Interrupt/Event software trigger on line 12"]
pub use Swiev0R as Swiev12R;
#[doc = "Field `SWIEV13` reader - Interrupt/Event software trigger on line 13"]
pub use Swiev0R as Swiev13R;
#[doc = "Field `SWIEV14` reader - Interrupt/Event software trigger on line 14"]
pub use Swiev0R as Swiev14R;
#[doc = "Field `SWIEV15` reader - Interrupt/Event software trigger on line 15"]
pub use Swiev0R as Swiev15R;
#[doc = "Field `SWIEV16` reader - Interrupt/Event software trigger on line 16"]
pub use Swiev0R as Swiev16R;
#[doc = "Field `SWIEV17` reader - Interrupt/Event software trigger on line 17"]
pub use Swiev0R as Swiev17R;
#[doc = "Field `SWIEV18` reader - Interrupt/Event software trigger on line 18"]
pub use Swiev0R as Swiev18R;
#[doc = "Field `SWIEV19` reader - Interrupt/Event software trigger on line 19"]
pub use Swiev0R as Swiev19R;
#[doc = "Field `SWIEV20` reader - Interrupt/Event software trigger on line 20"]
pub use Swiev0R as Swiev20R;
#[doc = "Field `SWIEV21` reader - Interrupt/Event software trigger on line 21"]
pub use Swiev0R as Swiev21R;
#[doc = "Field `SWIEV1` writer - Interrupt/Event software trigger on line 1"]
pub use Swiev0W as Swiev1W;
#[doc = "Field `SWIEV2` writer - Interrupt/Event software trigger on line 2"]
pub use Swiev0W as Swiev2W;
#[doc = "Field `SWIEV3` writer - Interrupt/Event software trigger on line 3"]
pub use Swiev0W as Swiev3W;
#[doc = "Field `SWIEV4` writer - Interrupt/Event software trigger on line 4"]
pub use Swiev0W as Swiev4W;
#[doc = "Field `SWIEV5` writer - Interrupt/Event software trigger on line 5"]
pub use Swiev0W as Swiev5W;
#[doc = "Field `SWIEV6` writer - Interrupt/Event software trigger on line 6"]
pub use Swiev0W as Swiev6W;
#[doc = "Field `SWIEV7` writer - Interrupt/Event software trigger on line 7"]
pub use Swiev0W as Swiev7W;
#[doc = "Field `SWIEV8` writer - Interrupt/Event software trigger on line 8"]
pub use Swiev0W as Swiev8W;
#[doc = "Field `SWIEV9` writer - Interrupt/Event software trigger on line 9"]
pub use Swiev0W as Swiev9W;
#[doc = "Field `SWIEV10` writer - Interrupt/Event software trigger on line 10"]
pub use Swiev0W as Swiev10W;
#[doc = "Field `SWIEV11` writer - Interrupt/Event software trigger on line 11"]
pub use Swiev0W as Swiev11W;
#[doc = "Field `SWIEV12` writer - Interrupt/Event software trigger on line 12"]
pub use Swiev0W as Swiev12W;
#[doc = "Field `SWIEV13` writer - Interrupt/Event software trigger on line 13"]
pub use Swiev0W as Swiev13W;
#[doc = "Field `SWIEV14` writer - Interrupt/Event software trigger on line 14"]
pub use Swiev0W as Swiev14W;
#[doc = "Field `SWIEV15` writer - Interrupt/Event software trigger on line 15"]
pub use Swiev0W as Swiev15W;
#[doc = "Field `SWIEV16` writer - Interrupt/Event software trigger on line 16"]
pub use Swiev0W as Swiev16W;
#[doc = "Field `SWIEV17` writer - Interrupt/Event software trigger on line 17"]
pub use Swiev0W as Swiev17W;
#[doc = "Field `SWIEV18` writer - Interrupt/Event software trigger on line 18"]
pub use Swiev0W as Swiev18W;
#[doc = "Field `SWIEV19` writer - Interrupt/Event software trigger on line 19"]
pub use Swiev0W as Swiev19W;
#[doc = "Field `SWIEV20` writer - Interrupt/Event software trigger on line 20"]
pub use Swiev0W as Swiev20W;
#[doc = "Field `SWIEV21` writer - Interrupt/Event software trigger on line 21"]
pub use Swiev0W as Swiev21W;
impl R {
    #[doc = "Bit 0 - Interrupt/Event software trigger on line 0"]
    #[inline(always)]
    pub fn swiev0(&self) -> Swiev0R {
        Swiev0R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Interrupt/Event software trigger on line 1"]
    #[inline(always)]
    pub fn swiev1(&self) -> Swiev1R {
        Swiev1R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Interrupt/Event software trigger on line 2"]
    #[inline(always)]
    pub fn swiev2(&self) -> Swiev2R {
        Swiev2R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Interrupt/Event software trigger on line 3"]
    #[inline(always)]
    pub fn swiev3(&self) -> Swiev3R {
        Swiev3R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Interrupt/Event software trigger on line 4"]
    #[inline(always)]
    pub fn swiev4(&self) -> Swiev4R {
        Swiev4R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Interrupt/Event software trigger on line 5"]
    #[inline(always)]
    pub fn swiev5(&self) -> Swiev5R {
        Swiev5R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Interrupt/Event software trigger on line 6"]
    #[inline(always)]
    pub fn swiev6(&self) -> Swiev6R {
        Swiev6R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Interrupt/Event software trigger on line 7"]
    #[inline(always)]
    pub fn swiev7(&self) -> Swiev7R {
        Swiev7R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Interrupt/Event software trigger on line 8"]
    #[inline(always)]
    pub fn swiev8(&self) -> Swiev8R {
        Swiev8R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Interrupt/Event software trigger on line 9"]
    #[inline(always)]
    pub fn swiev9(&self) -> Swiev9R {
        Swiev9R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Interrupt/Event software trigger on line 10"]
    #[inline(always)]
    pub fn swiev10(&self) -> Swiev10R {
        Swiev10R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Interrupt/Event software trigger on line 11"]
    #[inline(always)]
    pub fn swiev11(&self) -> Swiev11R {
        Swiev11R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Interrupt/Event software trigger on line 12"]
    #[inline(always)]
    pub fn swiev12(&self) -> Swiev12R {
        Swiev12R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Interrupt/Event software trigger on line 13"]
    #[inline(always)]
    pub fn swiev13(&self) -> Swiev13R {
        Swiev13R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Interrupt/Event software trigger on line 14"]
    #[inline(always)]
    pub fn swiev14(&self) -> Swiev14R {
        Swiev14R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Interrupt/Event software trigger on line 15"]
    #[inline(always)]
    pub fn swiev15(&self) -> Swiev15R {
        Swiev15R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - Interrupt/Event software trigger on line 16"]
    #[inline(always)]
    pub fn swiev16(&self) -> Swiev16R {
        Swiev16R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - Interrupt/Event software trigger on line 17"]
    #[inline(always)]
    pub fn swiev17(&self) -> Swiev17R {
        Swiev17R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - Interrupt/Event software trigger on line 18"]
    #[inline(always)]
    pub fn swiev18(&self) -> Swiev18R {
        Swiev18R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - Interrupt/Event software trigger on line 19"]
    #[inline(always)]
    pub fn swiev19(&self) -> Swiev19R {
        Swiev19R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - Interrupt/Event software trigger on line 20"]
    #[inline(always)]
    pub fn swiev20(&self) -> Swiev20R {
        Swiev20R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - Interrupt/Event software trigger on line 21"]
    #[inline(always)]
    pub fn swiev21(&self) -> Swiev21R {
        Swiev21R::new(((self.bits >> 21) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Interrupt/Event software trigger on line 0"]
    #[inline(always)]
    #[must_use]
    pub fn swiev0(&mut self) -> Swiev0W<SwievSpec> {
        Swiev0W::new(self, 0)
    }
    #[doc = "Bit 1 - Interrupt/Event software trigger on line 1"]
    #[inline(always)]
    #[must_use]
    pub fn swiev1(&mut self) -> Swiev1W<SwievSpec> {
        Swiev1W::new(self, 1)
    }
    #[doc = "Bit 2 - Interrupt/Event software trigger on line 2"]
    #[inline(always)]
    #[must_use]
    pub fn swiev2(&mut self) -> Swiev2W<SwievSpec> {
        Swiev2W::new(self, 2)
    }
    #[doc = "Bit 3 - Interrupt/Event software trigger on line 3"]
    #[inline(always)]
    #[must_use]
    pub fn swiev3(&mut self) -> Swiev3W<SwievSpec> {
        Swiev3W::new(self, 3)
    }
    #[doc = "Bit 4 - Interrupt/Event software trigger on line 4"]
    #[inline(always)]
    #[must_use]
    pub fn swiev4(&mut self) -> Swiev4W<SwievSpec> {
        Swiev4W::new(self, 4)
    }
    #[doc = "Bit 5 - Interrupt/Event software trigger on line 5"]
    #[inline(always)]
    #[must_use]
    pub fn swiev5(&mut self) -> Swiev5W<SwievSpec> {
        Swiev5W::new(self, 5)
    }
    #[doc = "Bit 6 - Interrupt/Event software trigger on line 6"]
    #[inline(always)]
    #[must_use]
    pub fn swiev6(&mut self) -> Swiev6W<SwievSpec> {
        Swiev6W::new(self, 6)
    }
    #[doc = "Bit 7 - Interrupt/Event software trigger on line 7"]
    #[inline(always)]
    #[must_use]
    pub fn swiev7(&mut self) -> Swiev7W<SwievSpec> {
        Swiev7W::new(self, 7)
    }
    #[doc = "Bit 8 - Interrupt/Event software trigger on line 8"]
    #[inline(always)]
    #[must_use]
    pub fn swiev8(&mut self) -> Swiev8W<SwievSpec> {
        Swiev8W::new(self, 8)
    }
    #[doc = "Bit 9 - Interrupt/Event software trigger on line 9"]
    #[inline(always)]
    #[must_use]
    pub fn swiev9(&mut self) -> Swiev9W<SwievSpec> {
        Swiev9W::new(self, 9)
    }
    #[doc = "Bit 10 - Interrupt/Event software trigger on line 10"]
    #[inline(always)]
    #[must_use]
    pub fn swiev10(&mut self) -> Swiev10W<SwievSpec> {
        Swiev10W::new(self, 10)
    }
    #[doc = "Bit 11 - Interrupt/Event software trigger on line 11"]
    #[inline(always)]
    #[must_use]
    pub fn swiev11(&mut self) -> Swiev11W<SwievSpec> {
        Swiev11W::new(self, 11)
    }
    #[doc = "Bit 12 - Interrupt/Event software trigger on line 12"]
    #[inline(always)]
    #[must_use]
    pub fn swiev12(&mut self) -> Swiev12W<SwievSpec> {
        Swiev12W::new(self, 12)
    }
    #[doc = "Bit 13 - Interrupt/Event software trigger on line 13"]
    #[inline(always)]
    #[must_use]
    pub fn swiev13(&mut self) -> Swiev13W<SwievSpec> {
        Swiev13W::new(self, 13)
    }
    #[doc = "Bit 14 - Interrupt/Event software trigger on line 14"]
    #[inline(always)]
    #[must_use]
    pub fn swiev14(&mut self) -> Swiev14W<SwievSpec> {
        Swiev14W::new(self, 14)
    }
    #[doc = "Bit 15 - Interrupt/Event software trigger on line 15"]
    #[inline(always)]
    #[must_use]
    pub fn swiev15(&mut self) -> Swiev15W<SwievSpec> {
        Swiev15W::new(self, 15)
    }
    #[doc = "Bit 16 - Interrupt/Event software trigger on line 16"]
    #[inline(always)]
    #[must_use]
    pub fn swiev16(&mut self) -> Swiev16W<SwievSpec> {
        Swiev16W::new(self, 16)
    }
    #[doc = "Bit 17 - Interrupt/Event software trigger on line 17"]
    #[inline(always)]
    #[must_use]
    pub fn swiev17(&mut self) -> Swiev17W<SwievSpec> {
        Swiev17W::new(self, 17)
    }
    #[doc = "Bit 18 - Interrupt/Event software trigger on line 18"]
    #[inline(always)]
    #[must_use]
    pub fn swiev18(&mut self) -> Swiev18W<SwievSpec> {
        Swiev18W::new(self, 18)
    }
    #[doc = "Bit 19 - Interrupt/Event software trigger on line 19"]
    #[inline(always)]
    #[must_use]
    pub fn swiev19(&mut self) -> Swiev19W<SwievSpec> {
        Swiev19W::new(self, 19)
    }
    #[doc = "Bit 20 - Interrupt/Event software trigger on line 20"]
    #[inline(always)]
    #[must_use]
    pub fn swiev20(&mut self) -> Swiev20W<SwievSpec> {
        Swiev20W::new(self, 20)
    }
    #[doc = "Bit 21 - Interrupt/Event software trigger on line 21"]
    #[inline(always)]
    #[must_use]
    pub fn swiev21(&mut self) -> Swiev21W<SwievSpec> {
        Swiev21W::new(self, 21)
    }
}
#[doc = "Software interrupt event register (EXTI_SWIEV)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`swiev::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`swiev::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SwievSpec;
impl crate::RegisterSpec for SwievSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`swiev::R`](R) reader structure"]
impl crate::Readable for SwievSpec {}
#[doc = "`write(|w| ..)` method takes [`swiev::W`](W) writer structure"]
impl crate::Writable for SwievSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets SWIEV to value 0"]
impl crate::Resettable for SwievSpec {
    const RESET_VALUE: u32 = 0;
}
