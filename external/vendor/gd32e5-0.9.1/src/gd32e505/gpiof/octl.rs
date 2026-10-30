#[doc = "Register `OCTL` reader"]
pub type R = crate::R<OctlSpec>;
#[doc = "Register `OCTL` writer"]
pub type W = crate::W<OctlSpec>;
#[doc = "Port output control\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Octl0 {
    #[doc = "0: Set output to logic low"]
    Low = 0,
    #[doc = "1: Set output to logic high"]
    High = 1,
}
impl From<Octl0> for bool {
    #[inline(always)]
    fn from(variant: Octl0) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `OCTL0` reader - Port output control"]
pub type Octl0R = crate::BitReader<Octl0>;
impl Octl0R {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Octl0 {
        match self.bits {
            false => Octl0::Low,
            true => Octl0::High,
        }
    }
    #[doc = "Set output to logic low"]
    #[inline(always)]
    pub fn is_low(&self) -> bool {
        *self == Octl0::Low
    }
    #[doc = "Set output to logic high"]
    #[inline(always)]
    pub fn is_high(&self) -> bool {
        *self == Octl0::High
    }
}
#[doc = "Field `OCTL0` writer - Port output control"]
pub type Octl0W<'a, REG> = crate::BitWriter<'a, REG, Octl0>;
impl<'a, REG> Octl0W<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Set output to logic low"]
    #[inline(always)]
    pub fn low(self) -> &'a mut crate::W<REG> {
        self.variant(Octl0::Low)
    }
    #[doc = "Set output to logic high"]
    #[inline(always)]
    pub fn high(self) -> &'a mut crate::W<REG> {
        self.variant(Octl0::High)
    }
}
#[doc = "Field `OCTL1` reader - Port output control"]
pub use Octl0R as Octl1R;
#[doc = "Field `OCTL2` reader - Port output control"]
pub use Octl0R as Octl2R;
#[doc = "Field `OCTL3` reader - Port output control"]
pub use Octl0R as Octl3R;
#[doc = "Field `OCTL4` reader - Port output control"]
pub use Octl0R as Octl4R;
#[doc = "Field `OCTL5` reader - Port output control"]
pub use Octl0R as Octl5R;
#[doc = "Field `OCTL6` reader - Port output control"]
pub use Octl0R as Octl6R;
#[doc = "Field `OCTL7` reader - Port output control"]
pub use Octl0R as Octl7R;
#[doc = "Field `OCTL8` reader - Port output control"]
pub use Octl0R as Octl8R;
#[doc = "Field `OCTL9` reader - Port output control"]
pub use Octl0R as Octl9R;
#[doc = "Field `OCTL10` reader - Port output control"]
pub use Octl0R as Octl10R;
#[doc = "Field `OCTL11` reader - Port output control"]
pub use Octl0R as Octl11R;
#[doc = "Field `OCTL12` reader - Port output control"]
pub use Octl0R as Octl12R;
#[doc = "Field `OCTL13` reader - Port output control"]
pub use Octl0R as Octl13R;
#[doc = "Field `OCTL14` reader - Port output control"]
pub use Octl0R as Octl14R;
#[doc = "Field `OCTL15` reader - Port output control"]
pub use Octl0R as Octl15R;
#[doc = "Field `OCTL1` writer - Port output control"]
pub use Octl0W as Octl1W;
#[doc = "Field `OCTL2` writer - Port output control"]
pub use Octl0W as Octl2W;
#[doc = "Field `OCTL3` writer - Port output control"]
pub use Octl0W as Octl3W;
#[doc = "Field `OCTL4` writer - Port output control"]
pub use Octl0W as Octl4W;
#[doc = "Field `OCTL5` writer - Port output control"]
pub use Octl0W as Octl5W;
#[doc = "Field `OCTL6` writer - Port output control"]
pub use Octl0W as Octl6W;
#[doc = "Field `OCTL7` writer - Port output control"]
pub use Octl0W as Octl7W;
#[doc = "Field `OCTL8` writer - Port output control"]
pub use Octl0W as Octl8W;
#[doc = "Field `OCTL9` writer - Port output control"]
pub use Octl0W as Octl9W;
#[doc = "Field `OCTL10` writer - Port output control"]
pub use Octl0W as Octl10W;
#[doc = "Field `OCTL11` writer - Port output control"]
pub use Octl0W as Octl11W;
#[doc = "Field `OCTL12` writer - Port output control"]
pub use Octl0W as Octl12W;
#[doc = "Field `OCTL13` writer - Port output control"]
pub use Octl0W as Octl13W;
#[doc = "Field `OCTL14` writer - Port output control"]
pub use Octl0W as Octl14W;
#[doc = "Field `OCTL15` writer - Port output control"]
pub use Octl0W as Octl15W;
impl R {
    #[doc = "Bit 0 - Port output control"]
    #[inline(always)]
    pub fn octl0(&self) -> Octl0R {
        Octl0R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Port output control"]
    #[inline(always)]
    pub fn octl1(&self) -> Octl1R {
        Octl1R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Port output control"]
    #[inline(always)]
    pub fn octl2(&self) -> Octl2R {
        Octl2R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Port output control"]
    #[inline(always)]
    pub fn octl3(&self) -> Octl3R {
        Octl3R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Port output control"]
    #[inline(always)]
    pub fn octl4(&self) -> Octl4R {
        Octl4R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Port output control"]
    #[inline(always)]
    pub fn octl5(&self) -> Octl5R {
        Octl5R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Port output control"]
    #[inline(always)]
    pub fn octl6(&self) -> Octl6R {
        Octl6R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Port output control"]
    #[inline(always)]
    pub fn octl7(&self) -> Octl7R {
        Octl7R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Port output control"]
    #[inline(always)]
    pub fn octl8(&self) -> Octl8R {
        Octl8R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Port output control"]
    #[inline(always)]
    pub fn octl9(&self) -> Octl9R {
        Octl9R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Port output control"]
    #[inline(always)]
    pub fn octl10(&self) -> Octl10R {
        Octl10R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Port output control"]
    #[inline(always)]
    pub fn octl11(&self) -> Octl11R {
        Octl11R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Port output control"]
    #[inline(always)]
    pub fn octl12(&self) -> Octl12R {
        Octl12R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Port output control"]
    #[inline(always)]
    pub fn octl13(&self) -> Octl13R {
        Octl13R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Port output control"]
    #[inline(always)]
    pub fn octl14(&self) -> Octl14R {
        Octl14R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Port output control"]
    #[inline(always)]
    pub fn octl15(&self) -> Octl15R {
        Octl15R::new(((self.bits >> 15) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Port output control"]
    #[inline(always)]
    #[must_use]
    pub fn octl0(&mut self) -> Octl0W<OctlSpec> {
        Octl0W::new(self, 0)
    }
    #[doc = "Bit 1 - Port output control"]
    #[inline(always)]
    #[must_use]
    pub fn octl1(&mut self) -> Octl1W<OctlSpec> {
        Octl1W::new(self, 1)
    }
    #[doc = "Bit 2 - Port output control"]
    #[inline(always)]
    #[must_use]
    pub fn octl2(&mut self) -> Octl2W<OctlSpec> {
        Octl2W::new(self, 2)
    }
    #[doc = "Bit 3 - Port output control"]
    #[inline(always)]
    #[must_use]
    pub fn octl3(&mut self) -> Octl3W<OctlSpec> {
        Octl3W::new(self, 3)
    }
    #[doc = "Bit 4 - Port output control"]
    #[inline(always)]
    #[must_use]
    pub fn octl4(&mut self) -> Octl4W<OctlSpec> {
        Octl4W::new(self, 4)
    }
    #[doc = "Bit 5 - Port output control"]
    #[inline(always)]
    #[must_use]
    pub fn octl5(&mut self) -> Octl5W<OctlSpec> {
        Octl5W::new(self, 5)
    }
    #[doc = "Bit 6 - Port output control"]
    #[inline(always)]
    #[must_use]
    pub fn octl6(&mut self) -> Octl6W<OctlSpec> {
        Octl6W::new(self, 6)
    }
    #[doc = "Bit 7 - Port output control"]
    #[inline(always)]
    #[must_use]
    pub fn octl7(&mut self) -> Octl7W<OctlSpec> {
        Octl7W::new(self, 7)
    }
    #[doc = "Bit 8 - Port output control"]
    #[inline(always)]
    #[must_use]
    pub fn octl8(&mut self) -> Octl8W<OctlSpec> {
        Octl8W::new(self, 8)
    }
    #[doc = "Bit 9 - Port output control"]
    #[inline(always)]
    #[must_use]
    pub fn octl9(&mut self) -> Octl9W<OctlSpec> {
        Octl9W::new(self, 9)
    }
    #[doc = "Bit 10 - Port output control"]
    #[inline(always)]
    #[must_use]
    pub fn octl10(&mut self) -> Octl10W<OctlSpec> {
        Octl10W::new(self, 10)
    }
    #[doc = "Bit 11 - Port output control"]
    #[inline(always)]
    #[must_use]
    pub fn octl11(&mut self) -> Octl11W<OctlSpec> {
        Octl11W::new(self, 11)
    }
    #[doc = "Bit 12 - Port output control"]
    #[inline(always)]
    #[must_use]
    pub fn octl12(&mut self) -> Octl12W<OctlSpec> {
        Octl12W::new(self, 12)
    }
    #[doc = "Bit 13 - Port output control"]
    #[inline(always)]
    #[must_use]
    pub fn octl13(&mut self) -> Octl13W<OctlSpec> {
        Octl13W::new(self, 13)
    }
    #[doc = "Bit 14 - Port output control"]
    #[inline(always)]
    #[must_use]
    pub fn octl14(&mut self) -> Octl14W<OctlSpec> {
        Octl14W::new(self, 14)
    }
    #[doc = "Bit 15 - Port output control"]
    #[inline(always)]
    #[must_use]
    pub fn octl15(&mut self) -> Octl15W<OctlSpec> {
        Octl15W::new(self, 15)
    }
}
#[doc = "Port output control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`octl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`octl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct OctlSpec;
impl crate::RegisterSpec for OctlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`octl::R`](R) reader structure"]
impl crate::Readable for OctlSpec {}
#[doc = "`write(|w| ..)` method takes [`octl::W`](W) writer structure"]
impl crate::Writable for OctlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets OCTL to value 0"]
impl crate::Resettable for OctlSpec {
    const RESET_VALUE: u32 = 0;
}
