#[doc = "Register `FW` reader"]
pub type R = crate::R<FwSpec>;
#[doc = "Register `FW` writer"]
pub type W = crate::W<FwSpec>;
#[doc = "Field `FW0` reader - Filter working"]
pub type Fw0R = crate::BitReader;
#[doc = "Field `FW0` writer - Filter working"]
pub type Fw0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FW1` reader - Filter working"]
pub type Fw1R = crate::BitReader;
#[doc = "Field `FW1` writer - Filter working"]
pub type Fw1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FW2` reader - Filter working"]
pub type Fw2R = crate::BitReader;
#[doc = "Field `FW2` writer - Filter working"]
pub type Fw2W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FW3` reader - Filter working"]
pub type Fw3R = crate::BitReader;
#[doc = "Field `FW3` writer - Filter working"]
pub type Fw3W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FW4` reader - Filter working"]
pub type Fw4R = crate::BitReader;
#[doc = "Field `FW4` writer - Filter working"]
pub type Fw4W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FW5` reader - Filter working"]
pub type Fw5R = crate::BitReader;
#[doc = "Field `FW5` writer - Filter working"]
pub type Fw5W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FW6` reader - Filter working"]
pub type Fw6R = crate::BitReader;
#[doc = "Field `FW6` writer - Filter working"]
pub type Fw6W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FW7` reader - Filter working"]
pub type Fw7R = crate::BitReader;
#[doc = "Field `FW7` writer - Filter working"]
pub type Fw7W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FW8` reader - Filter working"]
pub type Fw8R = crate::BitReader;
#[doc = "Field `FW8` writer - Filter working"]
pub type Fw8W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FW9` reader - Filter working"]
pub type Fw9R = crate::BitReader;
#[doc = "Field `FW9` writer - Filter working"]
pub type Fw9W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FW10` reader - Filter working"]
pub type Fw10R = crate::BitReader;
#[doc = "Field `FW10` writer - Filter working"]
pub type Fw10W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FW11` reader - Filter working"]
pub type Fw11R = crate::BitReader;
#[doc = "Field `FW11` writer - Filter working"]
pub type Fw11W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FW12` reader - Filter working"]
pub type Fw12R = crate::BitReader;
#[doc = "Field `FW12` writer - Filter working"]
pub type Fw12W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FW13` reader - Filter working"]
pub type Fw13R = crate::BitReader;
#[doc = "Field `FW13` writer - Filter working"]
pub type Fw13W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Filter working"]
    #[inline(always)]
    pub fn fw0(&self) -> Fw0R {
        Fw0R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Filter working"]
    #[inline(always)]
    pub fn fw1(&self) -> Fw1R {
        Fw1R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Filter working"]
    #[inline(always)]
    pub fn fw2(&self) -> Fw2R {
        Fw2R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Filter working"]
    #[inline(always)]
    pub fn fw3(&self) -> Fw3R {
        Fw3R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Filter working"]
    #[inline(always)]
    pub fn fw4(&self) -> Fw4R {
        Fw4R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Filter working"]
    #[inline(always)]
    pub fn fw5(&self) -> Fw5R {
        Fw5R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Filter working"]
    #[inline(always)]
    pub fn fw6(&self) -> Fw6R {
        Fw6R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Filter working"]
    #[inline(always)]
    pub fn fw7(&self) -> Fw7R {
        Fw7R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Filter working"]
    #[inline(always)]
    pub fn fw8(&self) -> Fw8R {
        Fw8R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Filter working"]
    #[inline(always)]
    pub fn fw9(&self) -> Fw9R {
        Fw9R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Filter working"]
    #[inline(always)]
    pub fn fw10(&self) -> Fw10R {
        Fw10R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Filter working"]
    #[inline(always)]
    pub fn fw11(&self) -> Fw11R {
        Fw11R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Filter working"]
    #[inline(always)]
    pub fn fw12(&self) -> Fw12R {
        Fw12R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Filter working"]
    #[inline(always)]
    pub fn fw13(&self) -> Fw13R {
        Fw13R::new(((self.bits >> 13) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Filter working"]
    #[inline(always)]
    #[must_use]
    pub fn fw0(&mut self) -> Fw0W<FwSpec> {
        Fw0W::new(self, 0)
    }
    #[doc = "Bit 1 - Filter working"]
    #[inline(always)]
    #[must_use]
    pub fn fw1(&mut self) -> Fw1W<FwSpec> {
        Fw1W::new(self, 1)
    }
    #[doc = "Bit 2 - Filter working"]
    #[inline(always)]
    #[must_use]
    pub fn fw2(&mut self) -> Fw2W<FwSpec> {
        Fw2W::new(self, 2)
    }
    #[doc = "Bit 3 - Filter working"]
    #[inline(always)]
    #[must_use]
    pub fn fw3(&mut self) -> Fw3W<FwSpec> {
        Fw3W::new(self, 3)
    }
    #[doc = "Bit 4 - Filter working"]
    #[inline(always)]
    #[must_use]
    pub fn fw4(&mut self) -> Fw4W<FwSpec> {
        Fw4W::new(self, 4)
    }
    #[doc = "Bit 5 - Filter working"]
    #[inline(always)]
    #[must_use]
    pub fn fw5(&mut self) -> Fw5W<FwSpec> {
        Fw5W::new(self, 5)
    }
    #[doc = "Bit 6 - Filter working"]
    #[inline(always)]
    #[must_use]
    pub fn fw6(&mut self) -> Fw6W<FwSpec> {
        Fw6W::new(self, 6)
    }
    #[doc = "Bit 7 - Filter working"]
    #[inline(always)]
    #[must_use]
    pub fn fw7(&mut self) -> Fw7W<FwSpec> {
        Fw7W::new(self, 7)
    }
    #[doc = "Bit 8 - Filter working"]
    #[inline(always)]
    #[must_use]
    pub fn fw8(&mut self) -> Fw8W<FwSpec> {
        Fw8W::new(self, 8)
    }
    #[doc = "Bit 9 - Filter working"]
    #[inline(always)]
    #[must_use]
    pub fn fw9(&mut self) -> Fw9W<FwSpec> {
        Fw9W::new(self, 9)
    }
    #[doc = "Bit 10 - Filter working"]
    #[inline(always)]
    #[must_use]
    pub fn fw10(&mut self) -> Fw10W<FwSpec> {
        Fw10W::new(self, 10)
    }
    #[doc = "Bit 11 - Filter working"]
    #[inline(always)]
    #[must_use]
    pub fn fw11(&mut self) -> Fw11W<FwSpec> {
        Fw11W::new(self, 11)
    }
    #[doc = "Bit 12 - Filter working"]
    #[inline(always)]
    #[must_use]
    pub fn fw12(&mut self) -> Fw12W<FwSpec> {
        Fw12W::new(self, 12)
    }
    #[doc = "Bit 13 - Filter working"]
    #[inline(always)]
    #[must_use]
    pub fn fw13(&mut self) -> Fw13W<FwSpec> {
        Fw13W::new(self, 13)
    }
}
#[doc = "Filter working register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`fw::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`fw::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct FwSpec;
impl crate::RegisterSpec for FwSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`fw::R`](R) reader structure"]
impl crate::Readable for FwSpec {}
#[doc = "`write(|w| ..)` method takes [`fw::W`](W) writer structure"]
impl crate::Writable for FwSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets FW to value 0"]
impl crate::Resettable for FwSpec {
    const RESET_VALUE: u32 = 0;
}
