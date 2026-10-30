#[doc = "Register `LOCK` reader"]
pub type R = crate::R<LockSpec>;
#[doc = "Register `LOCK` writer"]
pub type W = crate::W<LockSpec>;
#[doc = "Port Lock bit 0\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Lk0 {
    #[doc = "0: Port configuration not locked"]
    Unlocked = 0,
    #[doc = "1: Port configuration locked"]
    Locked = 1,
}
impl From<Lk0> for bool {
    #[inline(always)]
    fn from(variant: Lk0) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `LK0` reader - Port Lock bit 0"]
pub type Lk0R = crate::BitReader<Lk0>;
impl Lk0R {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Lk0 {
        match self.bits {
            false => Lk0::Unlocked,
            true => Lk0::Locked,
        }
    }
    #[doc = "Port configuration not locked"]
    #[inline(always)]
    pub fn is_unlocked(&self) -> bool {
        *self == Lk0::Unlocked
    }
    #[doc = "Port configuration locked"]
    #[inline(always)]
    pub fn is_locked(&self) -> bool {
        *self == Lk0::Locked
    }
}
#[doc = "Field `LK0` writer - Port Lock bit 0"]
pub type Lk0W<'a, REG> = crate::BitWriter<'a, REG, Lk0>;
impl<'a, REG> Lk0W<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Port configuration not locked"]
    #[inline(always)]
    pub fn unlocked(self) -> &'a mut crate::W<REG> {
        self.variant(Lk0::Unlocked)
    }
    #[doc = "Port configuration locked"]
    #[inline(always)]
    pub fn locked(self) -> &'a mut crate::W<REG> {
        self.variant(Lk0::Locked)
    }
}
#[doc = "Field `LK1` reader - Port Lock bit 1"]
pub use Lk0R as Lk1R;
#[doc = "Field `LK2` reader - Port Lock bit 2"]
pub use Lk0R as Lk2R;
#[doc = "Field `LK3` reader - Port Lock bit 3"]
pub use Lk0R as Lk3R;
#[doc = "Field `LK4` reader - Port Lock bit 4"]
pub use Lk0R as Lk4R;
#[doc = "Field `LK5` reader - Port Lock bit 5"]
pub use Lk0R as Lk5R;
#[doc = "Field `LK6` reader - Port Lock bit 6"]
pub use Lk0R as Lk6R;
#[doc = "Field `LK7` reader - Port Lock bit 7"]
pub use Lk0R as Lk7R;
#[doc = "Field `LK8` reader - Port Lock bit 8"]
pub use Lk0R as Lk8R;
#[doc = "Field `LK9` reader - Port Lock bit 9"]
pub use Lk0R as Lk9R;
#[doc = "Field `LK10` reader - Port Lock bit 10"]
pub use Lk0R as Lk10R;
#[doc = "Field `LK11` reader - Port Lock bit 11"]
pub use Lk0R as Lk11R;
#[doc = "Field `LK12` reader - Port Lock bit 12"]
pub use Lk0R as Lk12R;
#[doc = "Field `LK13` reader - Port Lock bit 13"]
pub use Lk0R as Lk13R;
#[doc = "Field `LK14` reader - Port Lock bit 14"]
pub use Lk0R as Lk14R;
#[doc = "Field `LK15` reader - Port Lock bit 15"]
pub use Lk0R as Lk15R;
#[doc = "Field `LK1` writer - Port Lock bit 1"]
pub use Lk0W as Lk1W;
#[doc = "Field `LK2` writer - Port Lock bit 2"]
pub use Lk0W as Lk2W;
#[doc = "Field `LK3` writer - Port Lock bit 3"]
pub use Lk0W as Lk3W;
#[doc = "Field `LK4` writer - Port Lock bit 4"]
pub use Lk0W as Lk4W;
#[doc = "Field `LK5` writer - Port Lock bit 5"]
pub use Lk0W as Lk5W;
#[doc = "Field `LK6` writer - Port Lock bit 6"]
pub use Lk0W as Lk6W;
#[doc = "Field `LK7` writer - Port Lock bit 7"]
pub use Lk0W as Lk7W;
#[doc = "Field `LK8` writer - Port Lock bit 8"]
pub use Lk0W as Lk8W;
#[doc = "Field `LK9` writer - Port Lock bit 9"]
pub use Lk0W as Lk9W;
#[doc = "Field `LK10` writer - Port Lock bit 10"]
pub use Lk0W as Lk10W;
#[doc = "Field `LK11` writer - Port Lock bit 11"]
pub use Lk0W as Lk11W;
#[doc = "Field `LK12` writer - Port Lock bit 12"]
pub use Lk0W as Lk12W;
#[doc = "Field `LK13` writer - Port Lock bit 13"]
pub use Lk0W as Lk13W;
#[doc = "Field `LK14` writer - Port Lock bit 14"]
pub use Lk0W as Lk14W;
#[doc = "Field `LK15` writer - Port Lock bit 15"]
pub use Lk0W as Lk15W;
#[doc = "Lock sequence key\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Lkk {
    #[doc = "0: Port configuration lock key not active"]
    NotActive = 0,
    #[doc = "1: Port configuration lock key active"]
    Active = 1,
}
impl From<Lkk> for bool {
    #[inline(always)]
    fn from(variant: Lkk) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `LKK` reader - Lock sequence key"]
pub type LkkR = crate::BitReader<Lkk>;
impl LkkR {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Lkk {
        match self.bits {
            false => Lkk::NotActive,
            true => Lkk::Active,
        }
    }
    #[doc = "Port configuration lock key not active"]
    #[inline(always)]
    pub fn is_not_active(&self) -> bool {
        *self == Lkk::NotActive
    }
    #[doc = "Port configuration lock key active"]
    #[inline(always)]
    pub fn is_active(&self) -> bool {
        *self == Lkk::Active
    }
}
#[doc = "Field `LKK` writer - Lock sequence key"]
pub type LkkW<'a, REG> = crate::BitWriter<'a, REG, Lkk>;
impl<'a, REG> LkkW<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Port configuration lock key not active"]
    #[inline(always)]
    pub fn not_active(self) -> &'a mut crate::W<REG> {
        self.variant(Lkk::NotActive)
    }
    #[doc = "Port configuration lock key active"]
    #[inline(always)]
    pub fn active(self) -> &'a mut crate::W<REG> {
        self.variant(Lkk::Active)
    }
}
impl R {
    #[doc = "Bit 0 - Port Lock bit 0"]
    #[inline(always)]
    pub fn lk0(&self) -> Lk0R {
        Lk0R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Port Lock bit 1"]
    #[inline(always)]
    pub fn lk1(&self) -> Lk1R {
        Lk1R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Port Lock bit 2"]
    #[inline(always)]
    pub fn lk2(&self) -> Lk2R {
        Lk2R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Port Lock bit 3"]
    #[inline(always)]
    pub fn lk3(&self) -> Lk3R {
        Lk3R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Port Lock bit 4"]
    #[inline(always)]
    pub fn lk4(&self) -> Lk4R {
        Lk4R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Port Lock bit 5"]
    #[inline(always)]
    pub fn lk5(&self) -> Lk5R {
        Lk5R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Port Lock bit 6"]
    #[inline(always)]
    pub fn lk6(&self) -> Lk6R {
        Lk6R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Port Lock bit 7"]
    #[inline(always)]
    pub fn lk7(&self) -> Lk7R {
        Lk7R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Port Lock bit 8"]
    #[inline(always)]
    pub fn lk8(&self) -> Lk8R {
        Lk8R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Port Lock bit 9"]
    #[inline(always)]
    pub fn lk9(&self) -> Lk9R {
        Lk9R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Port Lock bit 10"]
    #[inline(always)]
    pub fn lk10(&self) -> Lk10R {
        Lk10R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Port Lock bit 11"]
    #[inline(always)]
    pub fn lk11(&self) -> Lk11R {
        Lk11R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Port Lock bit 12"]
    #[inline(always)]
    pub fn lk12(&self) -> Lk12R {
        Lk12R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Port Lock bit 13"]
    #[inline(always)]
    pub fn lk13(&self) -> Lk13R {
        Lk13R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Port Lock bit 14"]
    #[inline(always)]
    pub fn lk14(&self) -> Lk14R {
        Lk14R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Port Lock bit 15"]
    #[inline(always)]
    pub fn lk15(&self) -> Lk15R {
        Lk15R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - Lock sequence key"]
    #[inline(always)]
    pub fn lkk(&self) -> LkkR {
        LkkR::new(((self.bits >> 16) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Port Lock bit 0"]
    #[inline(always)]
    #[must_use]
    pub fn lk0(&mut self) -> Lk0W<LockSpec> {
        Lk0W::new(self, 0)
    }
    #[doc = "Bit 1 - Port Lock bit 1"]
    #[inline(always)]
    #[must_use]
    pub fn lk1(&mut self) -> Lk1W<LockSpec> {
        Lk1W::new(self, 1)
    }
    #[doc = "Bit 2 - Port Lock bit 2"]
    #[inline(always)]
    #[must_use]
    pub fn lk2(&mut self) -> Lk2W<LockSpec> {
        Lk2W::new(self, 2)
    }
    #[doc = "Bit 3 - Port Lock bit 3"]
    #[inline(always)]
    #[must_use]
    pub fn lk3(&mut self) -> Lk3W<LockSpec> {
        Lk3W::new(self, 3)
    }
    #[doc = "Bit 4 - Port Lock bit 4"]
    #[inline(always)]
    #[must_use]
    pub fn lk4(&mut self) -> Lk4W<LockSpec> {
        Lk4W::new(self, 4)
    }
    #[doc = "Bit 5 - Port Lock bit 5"]
    #[inline(always)]
    #[must_use]
    pub fn lk5(&mut self) -> Lk5W<LockSpec> {
        Lk5W::new(self, 5)
    }
    #[doc = "Bit 6 - Port Lock bit 6"]
    #[inline(always)]
    #[must_use]
    pub fn lk6(&mut self) -> Lk6W<LockSpec> {
        Lk6W::new(self, 6)
    }
    #[doc = "Bit 7 - Port Lock bit 7"]
    #[inline(always)]
    #[must_use]
    pub fn lk7(&mut self) -> Lk7W<LockSpec> {
        Lk7W::new(self, 7)
    }
    #[doc = "Bit 8 - Port Lock bit 8"]
    #[inline(always)]
    #[must_use]
    pub fn lk8(&mut self) -> Lk8W<LockSpec> {
        Lk8W::new(self, 8)
    }
    #[doc = "Bit 9 - Port Lock bit 9"]
    #[inline(always)]
    #[must_use]
    pub fn lk9(&mut self) -> Lk9W<LockSpec> {
        Lk9W::new(self, 9)
    }
    #[doc = "Bit 10 - Port Lock bit 10"]
    #[inline(always)]
    #[must_use]
    pub fn lk10(&mut self) -> Lk10W<LockSpec> {
        Lk10W::new(self, 10)
    }
    #[doc = "Bit 11 - Port Lock bit 11"]
    #[inline(always)]
    #[must_use]
    pub fn lk11(&mut self) -> Lk11W<LockSpec> {
        Lk11W::new(self, 11)
    }
    #[doc = "Bit 12 - Port Lock bit 12"]
    #[inline(always)]
    #[must_use]
    pub fn lk12(&mut self) -> Lk12W<LockSpec> {
        Lk12W::new(self, 12)
    }
    #[doc = "Bit 13 - Port Lock bit 13"]
    #[inline(always)]
    #[must_use]
    pub fn lk13(&mut self) -> Lk13W<LockSpec> {
        Lk13W::new(self, 13)
    }
    #[doc = "Bit 14 - Port Lock bit 14"]
    #[inline(always)]
    #[must_use]
    pub fn lk14(&mut self) -> Lk14W<LockSpec> {
        Lk14W::new(self, 14)
    }
    #[doc = "Bit 15 - Port Lock bit 15"]
    #[inline(always)]
    #[must_use]
    pub fn lk15(&mut self) -> Lk15W<LockSpec> {
        Lk15W::new(self, 15)
    }
    #[doc = "Bit 16 - Lock sequence key"]
    #[inline(always)]
    #[must_use]
    pub fn lkk(&mut self) -> LkkW<LockSpec> {
        LkkW::new(self, 16)
    }
}
#[doc = "GPIO port configuration lock register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`lock::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`lock::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct LockSpec;
impl crate::RegisterSpec for LockSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`lock::R`](R) reader structure"]
impl crate::Readable for LockSpec {}
#[doc = "`write(|w| ..)` method takes [`lock::W`](W) writer structure"]
impl crate::Writable for LockSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets LOCK to value 0"]
impl crate::Resettable for LockSpec {
    const RESET_VALUE: u32 = 0;
}
