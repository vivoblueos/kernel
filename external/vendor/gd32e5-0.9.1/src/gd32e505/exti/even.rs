#[doc = "Register `EVEN` reader"]
pub type R = crate::R<EvenSpec>;
#[doc = "Register `EVEN` writer"]
pub type W = crate::W<EvenSpec>;
#[doc = "Enable Event on line 0\n\nValue on reset: 0"]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Even0 {
    #[doc = "0: Event from line is disabled"]
    Masked = 0,
    #[doc = "1: Event from line is enabled"]
    Unmasked = 1,
}
impl From<Even0> for bool {
    #[inline(always)]
    fn from(variant: Even0) -> Self {
        variant as u8 != 0
    }
}
#[doc = "Field `EVEN0` reader - Enable Event on line 0"]
pub type Even0R = crate::BitReader<Even0>;
impl Even0R {
    #[doc = "Get enumerated values variant"]
    #[inline(always)]
    pub const fn variant(&self) -> Even0 {
        match self.bits {
            false => Even0::Masked,
            true => Even0::Unmasked,
        }
    }
    #[doc = "Event from line is disabled"]
    #[inline(always)]
    pub fn is_masked(&self) -> bool {
        *self == Even0::Masked
    }
    #[doc = "Event from line is enabled"]
    #[inline(always)]
    pub fn is_unmasked(&self) -> bool {
        *self == Even0::Unmasked
    }
}
#[doc = "Field `EVEN0` writer - Enable Event on line 0"]
pub type Even0W<'a, REG> = crate::BitWriter<'a, REG, Even0>;
impl<'a, REG> Even0W<'a, REG>
where
    REG: crate::Writable + crate::RegisterSpec,
{
    #[doc = "Event from line is disabled"]
    #[inline(always)]
    pub fn masked(self) -> &'a mut crate::W<REG> {
        self.variant(Even0::Masked)
    }
    #[doc = "Event from line is enabled"]
    #[inline(always)]
    pub fn unmasked(self) -> &'a mut crate::W<REG> {
        self.variant(Even0::Unmasked)
    }
}
#[doc = "Field `EVEN1` reader - Enable Event on line 1"]
pub use Even0R as Even1R;
#[doc = "Field `EVEN2` reader - Enable Event on line 2"]
pub use Even0R as Even2R;
#[doc = "Field `EVEN3` reader - Enable Event on line 3"]
pub use Even0R as Even3R;
#[doc = "Field `EVEN4` reader - Enable Event on line 4"]
pub use Even0R as Even4R;
#[doc = "Field `EVEN5` reader - Enable Event on line 5"]
pub use Even0R as Even5R;
#[doc = "Field `EVEN6` reader - Enable Event on line 6"]
pub use Even0R as Even6R;
#[doc = "Field `EVEN7` reader - Enable Event on line 7"]
pub use Even0R as Even7R;
#[doc = "Field `EVEN8` reader - Enable Event on line 8"]
pub use Even0R as Even8R;
#[doc = "Field `EVEN9` reader - Enable Event on line 9"]
pub use Even0R as Even9R;
#[doc = "Field `EVEN10` reader - Enable Event on line 10"]
pub use Even0R as Even10R;
#[doc = "Field `EVEN11` reader - Enable Event on line 11"]
pub use Even0R as Even11R;
#[doc = "Field `EVEN12` reader - Enable Event on line 12"]
pub use Even0R as Even12R;
#[doc = "Field `EVEN13` reader - Enable Event on line 13"]
pub use Even0R as Even13R;
#[doc = "Field `EVEN14` reader - Enable Event on line 14"]
pub use Even0R as Even14R;
#[doc = "Field `EVEN15` reader - Enable Event on line 15"]
pub use Even0R as Even15R;
#[doc = "Field `EVEN16` reader - Enable Event on line 16"]
pub use Even0R as Even16R;
#[doc = "Field `EVEN17` reader - Enable Event on line 17"]
pub use Even0R as Even17R;
#[doc = "Field `EVEN18` reader - Enable Event on line 18"]
pub use Even0R as Even18R;
#[doc = "Field `EVEN19` reader - Enable Event on line 19"]
pub use Even0R as Even19R;
#[doc = "Field `EVEN20` reader - Enable Event on line 20"]
pub use Even0R as Even20R;
#[doc = "Field `EVEN21` reader - Enable Event on line 21"]
pub use Even0R as Even21R;
#[doc = "Field `EVEN1` writer - Enable Event on line 1"]
pub use Even0W as Even1W;
#[doc = "Field `EVEN2` writer - Enable Event on line 2"]
pub use Even0W as Even2W;
#[doc = "Field `EVEN3` writer - Enable Event on line 3"]
pub use Even0W as Even3W;
#[doc = "Field `EVEN4` writer - Enable Event on line 4"]
pub use Even0W as Even4W;
#[doc = "Field `EVEN5` writer - Enable Event on line 5"]
pub use Even0W as Even5W;
#[doc = "Field `EVEN6` writer - Enable Event on line 6"]
pub use Even0W as Even6W;
#[doc = "Field `EVEN7` writer - Enable Event on line 7"]
pub use Even0W as Even7W;
#[doc = "Field `EVEN8` writer - Enable Event on line 8"]
pub use Even0W as Even8W;
#[doc = "Field `EVEN9` writer - Enable Event on line 9"]
pub use Even0W as Even9W;
#[doc = "Field `EVEN10` writer - Enable Event on line 10"]
pub use Even0W as Even10W;
#[doc = "Field `EVEN11` writer - Enable Event on line 11"]
pub use Even0W as Even11W;
#[doc = "Field `EVEN12` writer - Enable Event on line 12"]
pub use Even0W as Even12W;
#[doc = "Field `EVEN13` writer - Enable Event on line 13"]
pub use Even0W as Even13W;
#[doc = "Field `EVEN14` writer - Enable Event on line 14"]
pub use Even0W as Even14W;
#[doc = "Field `EVEN15` writer - Enable Event on line 15"]
pub use Even0W as Even15W;
#[doc = "Field `EVEN16` writer - Enable Event on line 16"]
pub use Even0W as Even16W;
#[doc = "Field `EVEN17` writer - Enable Event on line 17"]
pub use Even0W as Even17W;
#[doc = "Field `EVEN18` writer - Enable Event on line 18"]
pub use Even0W as Even18W;
#[doc = "Field `EVEN19` writer - Enable Event on line 19"]
pub use Even0W as Even19W;
#[doc = "Field `EVEN20` writer - Enable Event on line 20"]
pub use Even0W as Even20W;
#[doc = "Field `EVEN21` writer - Enable Event on line 21"]
pub use Even0W as Even21W;
impl R {
    #[doc = "Bit 0 - Enable Event on line 0"]
    #[inline(always)]
    pub fn even0(&self) -> Even0R {
        Even0R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Enable Event on line 1"]
    #[inline(always)]
    pub fn even1(&self) -> Even1R {
        Even1R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Enable Event on line 2"]
    #[inline(always)]
    pub fn even2(&self) -> Even2R {
        Even2R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Enable Event on line 3"]
    #[inline(always)]
    pub fn even3(&self) -> Even3R {
        Even3R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Enable Event on line 4"]
    #[inline(always)]
    pub fn even4(&self) -> Even4R {
        Even4R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Enable Event on line 5"]
    #[inline(always)]
    pub fn even5(&self) -> Even5R {
        Even5R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Enable Event on line 6"]
    #[inline(always)]
    pub fn even6(&self) -> Even6R {
        Even6R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Enable Event on line 7"]
    #[inline(always)]
    pub fn even7(&self) -> Even7R {
        Even7R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Enable Event on line 8"]
    #[inline(always)]
    pub fn even8(&self) -> Even8R {
        Even8R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Enable Event on line 9"]
    #[inline(always)]
    pub fn even9(&self) -> Even9R {
        Even9R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Enable Event on line 10"]
    #[inline(always)]
    pub fn even10(&self) -> Even10R {
        Even10R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Enable Event on line 11"]
    #[inline(always)]
    pub fn even11(&self) -> Even11R {
        Even11R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Enable Event on line 12"]
    #[inline(always)]
    pub fn even12(&self) -> Even12R {
        Even12R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Enable Event on line 13"]
    #[inline(always)]
    pub fn even13(&self) -> Even13R {
        Even13R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Enable Event on line 14"]
    #[inline(always)]
    pub fn even14(&self) -> Even14R {
        Even14R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Enable Event on line 15"]
    #[inline(always)]
    pub fn even15(&self) -> Even15R {
        Even15R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - Enable Event on line 16"]
    #[inline(always)]
    pub fn even16(&self) -> Even16R {
        Even16R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - Enable Event on line 17"]
    #[inline(always)]
    pub fn even17(&self) -> Even17R {
        Even17R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - Enable Event on line 18"]
    #[inline(always)]
    pub fn even18(&self) -> Even18R {
        Even18R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - Enable Event on line 19"]
    #[inline(always)]
    pub fn even19(&self) -> Even19R {
        Even19R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - Enable Event on line 20"]
    #[inline(always)]
    pub fn even20(&self) -> Even20R {
        Even20R::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - Enable Event on line 21"]
    #[inline(always)]
    pub fn even21(&self) -> Even21R {
        Even21R::new(((self.bits >> 21) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Enable Event on line 0"]
    #[inline(always)]
    #[must_use]
    pub fn even0(&mut self) -> Even0W<EvenSpec> {
        Even0W::new(self, 0)
    }
    #[doc = "Bit 1 - Enable Event on line 1"]
    #[inline(always)]
    #[must_use]
    pub fn even1(&mut self) -> Even1W<EvenSpec> {
        Even1W::new(self, 1)
    }
    #[doc = "Bit 2 - Enable Event on line 2"]
    #[inline(always)]
    #[must_use]
    pub fn even2(&mut self) -> Even2W<EvenSpec> {
        Even2W::new(self, 2)
    }
    #[doc = "Bit 3 - Enable Event on line 3"]
    #[inline(always)]
    #[must_use]
    pub fn even3(&mut self) -> Even3W<EvenSpec> {
        Even3W::new(self, 3)
    }
    #[doc = "Bit 4 - Enable Event on line 4"]
    #[inline(always)]
    #[must_use]
    pub fn even4(&mut self) -> Even4W<EvenSpec> {
        Even4W::new(self, 4)
    }
    #[doc = "Bit 5 - Enable Event on line 5"]
    #[inline(always)]
    #[must_use]
    pub fn even5(&mut self) -> Even5W<EvenSpec> {
        Even5W::new(self, 5)
    }
    #[doc = "Bit 6 - Enable Event on line 6"]
    #[inline(always)]
    #[must_use]
    pub fn even6(&mut self) -> Even6W<EvenSpec> {
        Even6W::new(self, 6)
    }
    #[doc = "Bit 7 - Enable Event on line 7"]
    #[inline(always)]
    #[must_use]
    pub fn even7(&mut self) -> Even7W<EvenSpec> {
        Even7W::new(self, 7)
    }
    #[doc = "Bit 8 - Enable Event on line 8"]
    #[inline(always)]
    #[must_use]
    pub fn even8(&mut self) -> Even8W<EvenSpec> {
        Even8W::new(self, 8)
    }
    #[doc = "Bit 9 - Enable Event on line 9"]
    #[inline(always)]
    #[must_use]
    pub fn even9(&mut self) -> Even9W<EvenSpec> {
        Even9W::new(self, 9)
    }
    #[doc = "Bit 10 - Enable Event on line 10"]
    #[inline(always)]
    #[must_use]
    pub fn even10(&mut self) -> Even10W<EvenSpec> {
        Even10W::new(self, 10)
    }
    #[doc = "Bit 11 - Enable Event on line 11"]
    #[inline(always)]
    #[must_use]
    pub fn even11(&mut self) -> Even11W<EvenSpec> {
        Even11W::new(self, 11)
    }
    #[doc = "Bit 12 - Enable Event on line 12"]
    #[inline(always)]
    #[must_use]
    pub fn even12(&mut self) -> Even12W<EvenSpec> {
        Even12W::new(self, 12)
    }
    #[doc = "Bit 13 - Enable Event on line 13"]
    #[inline(always)]
    #[must_use]
    pub fn even13(&mut self) -> Even13W<EvenSpec> {
        Even13W::new(self, 13)
    }
    #[doc = "Bit 14 - Enable Event on line 14"]
    #[inline(always)]
    #[must_use]
    pub fn even14(&mut self) -> Even14W<EvenSpec> {
        Even14W::new(self, 14)
    }
    #[doc = "Bit 15 - Enable Event on line 15"]
    #[inline(always)]
    #[must_use]
    pub fn even15(&mut self) -> Even15W<EvenSpec> {
        Even15W::new(self, 15)
    }
    #[doc = "Bit 16 - Enable Event on line 16"]
    #[inline(always)]
    #[must_use]
    pub fn even16(&mut self) -> Even16W<EvenSpec> {
        Even16W::new(self, 16)
    }
    #[doc = "Bit 17 - Enable Event on line 17"]
    #[inline(always)]
    #[must_use]
    pub fn even17(&mut self) -> Even17W<EvenSpec> {
        Even17W::new(self, 17)
    }
    #[doc = "Bit 18 - Enable Event on line 18"]
    #[inline(always)]
    #[must_use]
    pub fn even18(&mut self) -> Even18W<EvenSpec> {
        Even18W::new(self, 18)
    }
    #[doc = "Bit 19 - Enable Event on line 19"]
    #[inline(always)]
    #[must_use]
    pub fn even19(&mut self) -> Even19W<EvenSpec> {
        Even19W::new(self, 19)
    }
    #[doc = "Bit 20 - Enable Event on line 20"]
    #[inline(always)]
    #[must_use]
    pub fn even20(&mut self) -> Even20W<EvenSpec> {
        Even20W::new(self, 20)
    }
    #[doc = "Bit 21 - Enable Event on line 21"]
    #[inline(always)]
    #[must_use]
    pub fn even21(&mut self) -> Even21W<EvenSpec> {
        Even21W::new(self, 21)
    }
}
#[doc = "Event enable register (EXTI_EVEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`even::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`even::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct EvenSpec;
impl crate::RegisterSpec for EvenSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`even::R`](R) reader structure"]
impl crate::Readable for EvenSpec {}
#[doc = "`write(|w| ..)` method takes [`even::W`](W) writer structure"]
impl crate::Writable for EvenSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets EVEN to value 0"]
impl crate::Resettable for EvenSpec {
    const RESET_VALUE: u32 = 0;
}
