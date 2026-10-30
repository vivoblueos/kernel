#[doc = "Register `LOCK` reader"]
pub type R = crate::R<LockSpec>;
#[doc = "Register `LOCK` writer"]
pub type W = crate::W<LockSpec>;
#[doc = "Field `LK0` reader - Port Lock bit 0"]
pub type Lk0R = crate::BitReader;
#[doc = "Field `LK0` writer - Port Lock bit 0"]
pub type Lk0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LK1` reader - Port Lock bit 1"]
pub type Lk1R = crate::BitReader;
#[doc = "Field `LK1` writer - Port Lock bit 1"]
pub type Lk1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LK2` reader - Port Lock bit 2"]
pub type Lk2R = crate::BitReader;
#[doc = "Field `LK2` writer - Port Lock bit 2"]
pub type Lk2W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LK3` reader - Port Lock bit 3"]
pub type Lk3R = crate::BitReader;
#[doc = "Field `LK3` writer - Port Lock bit 3"]
pub type Lk3W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LK4` reader - Port Lock bit 4"]
pub type Lk4R = crate::BitReader;
#[doc = "Field `LK4` writer - Port Lock bit 4"]
pub type Lk4W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LK5` reader - Port Lock bit 5"]
pub type Lk5R = crate::BitReader;
#[doc = "Field `LK5` writer - Port Lock bit 5"]
pub type Lk5W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LK6` reader - Port Lock bit 6"]
pub type Lk6R = crate::BitReader;
#[doc = "Field `LK6` writer - Port Lock bit 6"]
pub type Lk6W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LK7` reader - Port Lock bit 7"]
pub type Lk7R = crate::BitReader;
#[doc = "Field `LK7` writer - Port Lock bit 7"]
pub type Lk7W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LK8` reader - Port Lock bit 8"]
pub type Lk8R = crate::BitReader;
#[doc = "Field `LK8` writer - Port Lock bit 8"]
pub type Lk8W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LK9` reader - Port Lock bit 9"]
pub type Lk9R = crate::BitReader;
#[doc = "Field `LK9` writer - Port Lock bit 9"]
pub type Lk9W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LK10` reader - Port Lock bit 10"]
pub type Lk10R = crate::BitReader;
#[doc = "Field `LK10` writer - Port Lock bit 10"]
pub type Lk10W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LK11` reader - Port Lock bit 11"]
pub type Lk11R = crate::BitReader;
#[doc = "Field `LK11` writer - Port Lock bit 11"]
pub type Lk11W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LK12` reader - Port Lock bit 12"]
pub type Lk12R = crate::BitReader;
#[doc = "Field `LK12` writer - Port Lock bit 12"]
pub type Lk12W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LK13` reader - Port Lock bit 13"]
pub type Lk13R = crate::BitReader;
#[doc = "Field `LK13` writer - Port Lock bit 13"]
pub type Lk13W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LK14` reader - Port Lock bit 14"]
pub type Lk14R = crate::BitReader;
#[doc = "Field `LK14` writer - Port Lock bit 14"]
pub type Lk14W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LK15` reader - Port Lock bit 15"]
pub type Lk15R = crate::BitReader;
#[doc = "Field `LK15` writer - Port Lock bit 15"]
pub type Lk15W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LKK` reader - Lock sequence key"]
pub type LkkR = crate::BitReader;
#[doc = "Field `LKK` writer - Lock sequence key"]
pub type LkkW<'a, REG> = crate::BitWriter<'a, REG>;
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
