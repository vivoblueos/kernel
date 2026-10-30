#[doc = "Register `PD` reader"]
pub type R = crate::R<PdSpec>;
#[doc = "Register `PD` writer"]
pub type W = crate::W<PdSpec>;
#[doc = "Interrupt pending status of line 0\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Pd0r {
    #[doc = "0: No trigger request occurred"]
    NotPending = 0,
    #[doc = "1: Selected trigger request occurred"]
    Pending = 1,
}
impl From<Pd0r> for bool {
    #[inline(always)]
    fn from(variant: Pd0r) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `PD0` reader - Interrupt pending status of line 0"]
pub type Pd0R = crate::BitReader<Pd0r>;
impl Pd0R {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Pd0r {
        match self.bits {
            false => Pd0r::NotPending,
            true => Pd0r::Pending,
        }
    }
    #[doc = "No trigger request occurred"]
    #[inline(always)]
    pub fn is_not_pending(&self) -> bool {
        *self == Pd0r::NotPending
    }
    #[doc = "Selected trigger request occurred"]
    #[inline(always)]
    pub fn is_pending(&self) -> bool {
        *self == Pd0r::Pending
    }
}
#[doc = "Interrupt pending status of line 0\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Pd0wWO {
    #[doc = "1: Clears pending bit"]
    Clear = 1,
}
impl From<Pd0wWO> for bool {
    #[inline(always)]
    fn from(variant: Pd0wWO) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `PD0` writer - Interrupt pending status of line 0"]
pub type Pd0W<'a, REG> = crate::BitWriter<'a, REG, Pd0wWO>;
impl<'a, REG> Pd0W<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Clears pending bit"]
    #[inline(always)]
    pub fn clear(self) -> &'a mut crate::W<REG> {
        self.variant(Pd0wWO::Clear)
    }
}
#[doc = "Field `PD1` reader - Interrupt pending status of line 1"]
pub use Pd0R as Pd1R;
#[doc = "Field `PD2` reader - Interrupt pending status of line 2"]
pub use Pd0R as Pd2R;
#[doc = "Field `PD3` reader - Interrupt pending status of line 3"]
pub use Pd0R as Pd3R;
#[doc = "Field `PD4` reader - Interrupt pending status of line 4"]
pub use Pd0R as Pd4R;
#[doc = "Field `PD5` reader - Interrupt pending status of line 5"]
pub use Pd0R as Pd5R;
#[doc = "Field `PD6` reader - Interrupt pending status of line 6"]
pub use Pd0R as Pd6R;
#[doc = "Field `PD7` reader - Interrupt pending status of line 7"]
pub use Pd0R as Pd7R;
#[doc = "Field `PD8` reader - Interrupt pending status of line 8"]
pub use Pd0R as Pd8R;
#[doc = "Field `PD9` reader - Interrupt pending status of line 9"]
pub use Pd0R as Pd9R;
#[doc = "Field `PD10` reader - Interrupt pending status of line 10"]
pub use Pd0R as Pd10R;
#[doc = "Field `PD11` reader - Interrupt pending status of line 11"]
pub use Pd0R as Pd11R;
#[doc = "Field `PD12` reader - Interrupt pending status of line 12"]
pub use Pd0R as Pd12R;
#[doc = "Field `PD13` reader - Interrupt pending status of line 13"]
pub use Pd0R as Pd13R;
#[doc = "Field `PD14` reader - Interrupt pending status of line 14"]
pub use Pd0R as Pd14R;
#[doc = "Field `PD15` reader - Interrupt pending status of line 15"]
pub use Pd0R as Pd15R;
#[doc = "Field `PD16` reader - Interrupt pending status of line 16"]
pub use Pd0R as Pd16R;
#[doc = "Field `PD17` reader - Interrupt pending status of line 17"]
pub use Pd0R as Pd17R;
#[doc = "Field `PD18` reader - Interrupt pending status of line 18"]
pub use Pd0R as Pd18R;
#[doc = "Field `PD19` reader - Interrupt pending status of line 19"]
pub use Pd0R as Pd19R;
#[doc = "Field `PD20` reader - Interrupt pending status of line 20"]
pub use Pd0R as Pd20R;
#[doc = "Field `PD21` reader - Interrupt pending status of line 21"]
pub use Pd0R as Pd21R;
#[doc = "Field `PD1` writer - Interrupt pending status of line 1"]
pub use Pd0W as Pd1W;
#[doc = "Field `PD2` writer - Interrupt pending status of line 2"]
pub use Pd0W as Pd2W;
#[doc = "Field `PD3` writer - Interrupt pending status of line 3"]
pub use Pd0W as Pd3W;
#[doc = "Field `PD4` writer - Interrupt pending status of line 4"]
pub use Pd0W as Pd4W;
#[doc = "Field `PD5` writer - Interrupt pending status of line 5"]
pub use Pd0W as Pd5W;
#[doc = "Field `PD6` writer - Interrupt pending status of line 6"]
pub use Pd0W as Pd6W;
#[doc = "Field `PD7` writer - Interrupt pending status of line 7"]
pub use Pd0W as Pd7W;
#[doc = "Field `PD8` writer - Interrupt pending status of line 8"]
pub use Pd0W as Pd8W;
#[doc = "Field `PD9` writer - Interrupt pending status of line 9"]
pub use Pd0W as Pd9W;
#[doc = "Field `PD10` writer - Interrupt pending status of line 10"]
pub use Pd0W as Pd10W;
#[doc = "Field `PD11` writer - Interrupt pending status of line 11"]
pub use Pd0W as Pd11W;
#[doc = "Field `PD12` writer - Interrupt pending status of line 12"]
pub use Pd0W as Pd12W;
#[doc = "Field `PD13` writer - Interrupt pending status of line 13"]
pub use Pd0W as Pd13W;
#[doc = "Field `PD14` writer - Interrupt pending status of line 14"]
pub use Pd0W as Pd14W;
#[doc = "Field `PD15` writer - Interrupt pending status of line 15"]
pub use Pd0W as Pd15W;
#[doc = "Field `PD16` writer - Interrupt pending status of line 16"]
pub use Pd0W as Pd16W;
#[doc = "Field `PD17` writer - Interrupt pending status of line 17"]
pub use Pd0W as Pd17W;
#[doc = "Field `PD18` writer - Interrupt pending status of line 18"]
pub use Pd0W as Pd18W;
#[doc = "Field `PD19` writer - Interrupt pending status of line 19"]
pub use Pd0W as Pd19W;
#[doc = "Field `PD20` writer - Interrupt pending status of line 20"]
pub use Pd0W as Pd20W;
#[doc = "Field `PD21` writer - Interrupt pending status of line 21"]
pub use Pd0W as Pd21W;
impl R {
    #[doc = "Bit 0 - Interrupt pending status of line 0"]
    #[inline(always)]
    pub fn pd0(&self) -> Pd0R {
        Pd0R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Interrupt pending status of line 1"]
    #[inline(always)]
    pub fn pd1(&self) -> Pd1R {
        Pd1R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Interrupt pending status of line 2"]
    #[inline(always)]
    pub fn pd2(&self) -> Pd2R {
        Pd2R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Interrupt pending status of line 3"]
    #[inline(always)]
    pub fn pd3(&self) -> Pd3R {
        Pd3R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Interrupt pending status of line 4"]
    #[inline(always)]
    pub fn pd4(&self) -> Pd4R {
        Pd4R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Interrupt pending status of line 5"]
    #[inline(always)]
    pub fn pd5(&self) -> Pd5R {
        Pd5R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Interrupt pending status of line 6"]
    #[inline(always)]
    pub fn pd6(&self) -> Pd6R {
        Pd6R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Interrupt pending status of line 7"]
    #[inline(always)]
    pub fn pd7(&self) -> Pd7R {
        Pd7R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Interrupt pending status of line 8"]
    #[inline(always)]
    pub fn pd8(&self) -> Pd8R {
        Pd8R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Interrupt pending status of line 9"]
    #[inline(always)]
    pub fn pd9(&self) -> Pd9R {
        Pd9R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Interrupt pending status of line 10"]
    #[inline(always)]
    pub fn pd10(&self) -> Pd10R {
        Pd10R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Interrupt pending status of line 11"]
    #[inline(always)]
    pub fn pd11(&self) -> Pd11R {
        Pd11R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Interrupt pending status of line 12"]
    #[inline(always)]
    pub fn pd12(&self) -> Pd12R {
        Pd12R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Interrupt pending status of line 13"]
    #[inline(always)]
    pub fn pd13(&self) -> Pd13R {
        Pd13R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Interrupt pending status of line 14"]
    #[inline(always)]
    pub fn pd14(&self) -> Pd14R {
        Pd14R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Interrupt pending status of line 15"]
    #[inline(always)]
    pub fn pd15(&self) -> Pd15R {
        Pd15R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - Interrupt pending status of line 16"]
    #[inline(always)]
    pub fn pd16(&self) -> Pd16R {
        Pd16R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - Interrupt pending status of line 17"]
    #[inline(always)]
    pub fn pd17(&self) -> Pd17R {
        Pd17R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - Interrupt pending status of line 18"]
    #[inline(always)]
    pub fn pd18(&self) -> Pd18R {
        Pd18R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - Interrupt pending status of line 19"]
    #[inline(always)]
    pub fn pd19(&self) -> Pd19R {
        Pd19R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - Interrupt pending status of line 20"]
    #[inline(always)]
    pub fn pd20(&self) -> Pd20R {
        Pd20R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - Interrupt pending status of line 21"]
    #[inline(always)]
    pub fn pd21(&self) -> Pd21R {
        Pd21R::new(((self.bits >> 21) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Interrupt pending status of line 0"]
    #[inline(always)]
    #[must_use]
    pub fn pd0(&mut self) -> Pd0W<PdSpec> {
        Pd0W::new(self, 0)
    }
    #[doc = "Bit 1 - Interrupt pending status of line 1"]
    #[inline(always)]
    #[must_use]
    pub fn pd1(&mut self) -> Pd1W<PdSpec> {
        Pd1W::new(self, 1)
    }
    #[doc = "Bit 2 - Interrupt pending status of line 2"]
    #[inline(always)]
    #[must_use]
    pub fn pd2(&mut self) -> Pd2W<PdSpec> {
        Pd2W::new(self, 2)
    }
    #[doc = "Bit 3 - Interrupt pending status of line 3"]
    #[inline(always)]
    #[must_use]
    pub fn pd3(&mut self) -> Pd3W<PdSpec> {
        Pd3W::new(self, 3)
    }
    #[doc = "Bit 4 - Interrupt pending status of line 4"]
    #[inline(always)]
    #[must_use]
    pub fn pd4(&mut self) -> Pd4W<PdSpec> {
        Pd4W::new(self, 4)
    }
    #[doc = "Bit 5 - Interrupt pending status of line 5"]
    #[inline(always)]
    #[must_use]
    pub fn pd5(&mut self) -> Pd5W<PdSpec> {
        Pd5W::new(self, 5)
    }
    #[doc = "Bit 6 - Interrupt pending status of line 6"]
    #[inline(always)]
    #[must_use]
    pub fn pd6(&mut self) -> Pd6W<PdSpec> {
        Pd6W::new(self, 6)
    }
    #[doc = "Bit 7 - Interrupt pending status of line 7"]
    #[inline(always)]
    #[must_use]
    pub fn pd7(&mut self) -> Pd7W<PdSpec> {
        Pd7W::new(self, 7)
    }
    #[doc = "Bit 8 - Interrupt pending status of line 8"]
    #[inline(always)]
    #[must_use]
    pub fn pd8(&mut self) -> Pd8W<PdSpec> {
        Pd8W::new(self, 8)
    }
    #[doc = "Bit 9 - Interrupt pending status of line 9"]
    #[inline(always)]
    #[must_use]
    pub fn pd9(&mut self) -> Pd9W<PdSpec> {
        Pd9W::new(self, 9)
    }
    #[doc = "Bit 10 - Interrupt pending status of line 10"]
    #[inline(always)]
    #[must_use]
    pub fn pd10(&mut self) -> Pd10W<PdSpec> {
        Pd10W::new(self, 10)
    }
    #[doc = "Bit 11 - Interrupt pending status of line 11"]
    #[inline(always)]
    #[must_use]
    pub fn pd11(&mut self) -> Pd11W<PdSpec> {
        Pd11W::new(self, 11)
    }
    #[doc = "Bit 12 - Interrupt pending status of line 12"]
    #[inline(always)]
    #[must_use]
    pub fn pd12(&mut self) -> Pd12W<PdSpec> {
        Pd12W::new(self, 12)
    }
    #[doc = "Bit 13 - Interrupt pending status of line 13"]
    #[inline(always)]
    #[must_use]
    pub fn pd13(&mut self) -> Pd13W<PdSpec> {
        Pd13W::new(self, 13)
    }
    #[doc = "Bit 14 - Interrupt pending status of line 14"]
    #[inline(always)]
    #[must_use]
    pub fn pd14(&mut self) -> Pd14W<PdSpec> {
        Pd14W::new(self, 14)
    }
    #[doc = "Bit 15 - Interrupt pending status of line 15"]
    #[inline(always)]
    #[must_use]
    pub fn pd15(&mut self) -> Pd15W<PdSpec> {
        Pd15W::new(self, 15)
    }
    #[doc = "Bit 16 - Interrupt pending status of line 16"]
    #[inline(always)]
    #[must_use]
    pub fn pd16(&mut self) -> Pd16W<PdSpec> {
        Pd16W::new(self, 16)
    }
    #[doc = "Bit 17 - Interrupt pending status of line 17"]
    #[inline(always)]
    #[must_use]
    pub fn pd17(&mut self) -> Pd17W<PdSpec> {
        Pd17W::new(self, 17)
    }
    #[doc = "Bit 18 - Interrupt pending status of line 18"]
    #[inline(always)]
    #[must_use]
    pub fn pd18(&mut self) -> Pd18W<PdSpec> {
        Pd18W::new(self, 18)
    }
    #[doc = "Bit 19 - Interrupt pending status of line 19"]
    #[inline(always)]
    #[must_use]
    pub fn pd19(&mut self) -> Pd19W<PdSpec> {
        Pd19W::new(self, 19)
    }
    #[doc = "Bit 20 - Interrupt pending status of line 20"]
    #[inline(always)]
    #[must_use]
    pub fn pd20(&mut self) -> Pd20W<PdSpec> {
        Pd20W::new(self, 20)
    }
    #[doc = "Bit 21 - Interrupt pending status of line 21"]
    #[inline(always)]
    #[must_use]
    pub fn pd21(&mut self) -> Pd21W<PdSpec> {
        Pd21W::new(self, 21)
    }
}
#[doc = "Pending register (EXTI_PD)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`pd::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`pd::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PdSpec;
impl crate::RegisterSpec for PdSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`pd::R`](R) reader structure"]
impl crate::Readable for PdSpec {}
#[doc = "`write(|w| ..)` method takes [`pd::W`](W) writer structure"]
impl crate::Writable for PdSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets PD to value 0"]
impl crate::Resettable for PdSpec {
    const RESET_VALUE: u32 = 0;
}
