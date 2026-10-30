#[doc = "Register `FAFIFO` reader"]
pub type R = crate::R<FafifoSpec>;
#[doc = "Register `FAFIFO` writer"]
pub type W = crate::W<FafifoSpec>;
#[doc = "Field `FAF0` reader - Filter 0 associated with FIFO"]
pub type Faf0R = crate::BitReader;
#[doc = "Field `FAF0` writer - Filter 0 associated with FIFO"]
pub type Faf0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FAF1` reader - Filter 1 associated with FIFO"]
pub type Faf1R = crate::BitReader;
#[doc = "Field `FAF1` writer - Filter 1 associated with FIFO"]
pub type Faf1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FAF2` reader - Filter 2 associated with FIFO"]
pub type Faf2R = crate::BitReader;
#[doc = "Field `FAF2` writer - Filter 2 associated with FIFO"]
pub type Faf2W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FAF3` reader - Filter 3 associated with FIFO"]
pub type Faf3R = crate::BitReader;
#[doc = "Field `FAF3` writer - Filter 3 associated with FIFO"]
pub type Faf3W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FAF4` reader - Filter 4 associated with FIFO"]
pub type Faf4R = crate::BitReader;
#[doc = "Field `FAF4` writer - Filter 4 associated with FIFO"]
pub type Faf4W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FAF5` reader - Filter 5 associated with FIFO"]
pub type Faf5R = crate::BitReader;
#[doc = "Field `FAF5` writer - Filter 5 associated with FIFO"]
pub type Faf5W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FAF6` reader - Filter 6 associated with FIFO"]
pub type Faf6R = crate::BitReader;
#[doc = "Field `FAF6` writer - Filter 6 associated with FIFO"]
pub type Faf6W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FAF7` reader - Filter 7 associated with FIFO"]
pub type Faf7R = crate::BitReader;
#[doc = "Field `FAF7` writer - Filter 7 associated with FIFO"]
pub type Faf7W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FAF8` reader - Filter 8 associated with FIFO"]
pub type Faf8R = crate::BitReader;
#[doc = "Field `FAF8` writer - Filter 8 associated with FIFO"]
pub type Faf8W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FAF9` reader - Filter 9 associated with FIFO"]
pub type Faf9R = crate::BitReader;
#[doc = "Field `FAF9` writer - Filter 9 associated with FIFO"]
pub type Faf9W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FAF10` reader - Filter 10 associated with FIFO"]
pub type Faf10R = crate::BitReader;
#[doc = "Field `FAF10` writer - Filter 10 associated with FIFO"]
pub type Faf10W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FAF11` reader - Filter 11 associated with FIFO"]
pub type Faf11R = crate::BitReader;
#[doc = "Field `FAF11` writer - Filter 11 associated with FIFO"]
pub type Faf11W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FAF12` reader - Filter 12 associated with FIFO"]
pub type Faf12R = crate::BitReader;
#[doc = "Field `FAF12` writer - Filter 12 associated with FIFO"]
pub type Faf12W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FAF13` reader - Filter 13 associated with FIFO"]
pub type Faf13R = crate::BitReader;
#[doc = "Field `FAF13` writer - Filter 13 associated with FIFO"]
pub type Faf13W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Filter 0 associated with FIFO"]
    #[inline(always)]
    pub fn faf0(&self) -> Faf0R {
        Faf0R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Filter 1 associated with FIFO"]
    #[inline(always)]
    pub fn faf1(&self) -> Faf1R {
        Faf1R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Filter 2 associated with FIFO"]
    #[inline(always)]
    pub fn faf2(&self) -> Faf2R {
        Faf2R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Filter 3 associated with FIFO"]
    #[inline(always)]
    pub fn faf3(&self) -> Faf3R {
        Faf3R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Filter 4 associated with FIFO"]
    #[inline(always)]
    pub fn faf4(&self) -> Faf4R {
        Faf4R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Filter 5 associated with FIFO"]
    #[inline(always)]
    pub fn faf5(&self) -> Faf5R {
        Faf5R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Filter 6 associated with FIFO"]
    #[inline(always)]
    pub fn faf6(&self) -> Faf6R {
        Faf6R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Filter 7 associated with FIFO"]
    #[inline(always)]
    pub fn faf7(&self) -> Faf7R {
        Faf7R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Filter 8 associated with FIFO"]
    #[inline(always)]
    pub fn faf8(&self) -> Faf8R {
        Faf8R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Filter 9 associated with FIFO"]
    #[inline(always)]
    pub fn faf9(&self) -> Faf9R {
        Faf9R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Filter 10 associated with FIFO"]
    #[inline(always)]
    pub fn faf10(&self) -> Faf10R {
        Faf10R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Filter 11 associated with FIFO"]
    #[inline(always)]
    pub fn faf11(&self) -> Faf11R {
        Faf11R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Filter 12 associated with FIFO"]
    #[inline(always)]
    pub fn faf12(&self) -> Faf12R {
        Faf12R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Filter 13 associated with FIFO"]
    #[inline(always)]
    pub fn faf13(&self) -> Faf13R {
        Faf13R::new(((self.bits >> 13) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Filter 0 associated with FIFO"]
    #[inline(always)]
    #[must_use]
    pub fn faf0(&mut self) -> Faf0W<FafifoSpec> {
        Faf0W::new(self, 0)
    }
    #[doc = "Bit 1 - Filter 1 associated with FIFO"]
    #[inline(always)]
    #[must_use]
    pub fn faf1(&mut self) -> Faf1W<FafifoSpec> {
        Faf1W::new(self, 1)
    }
    #[doc = "Bit 2 - Filter 2 associated with FIFO"]
    #[inline(always)]
    #[must_use]
    pub fn faf2(&mut self) -> Faf2W<FafifoSpec> {
        Faf2W::new(self, 2)
    }
    #[doc = "Bit 3 - Filter 3 associated with FIFO"]
    #[inline(always)]
    #[must_use]
    pub fn faf3(&mut self) -> Faf3W<FafifoSpec> {
        Faf3W::new(self, 3)
    }
    #[doc = "Bit 4 - Filter 4 associated with FIFO"]
    #[inline(always)]
    #[must_use]
    pub fn faf4(&mut self) -> Faf4W<FafifoSpec> {
        Faf4W::new(self, 4)
    }
    #[doc = "Bit 5 - Filter 5 associated with FIFO"]
    #[inline(always)]
    #[must_use]
    pub fn faf5(&mut self) -> Faf5W<FafifoSpec> {
        Faf5W::new(self, 5)
    }
    #[doc = "Bit 6 - Filter 6 associated with FIFO"]
    #[inline(always)]
    #[must_use]
    pub fn faf6(&mut self) -> Faf6W<FafifoSpec> {
        Faf6W::new(self, 6)
    }
    #[doc = "Bit 7 - Filter 7 associated with FIFO"]
    #[inline(always)]
    #[must_use]
    pub fn faf7(&mut self) -> Faf7W<FafifoSpec> {
        Faf7W::new(self, 7)
    }
    #[doc = "Bit 8 - Filter 8 associated with FIFO"]
    #[inline(always)]
    #[must_use]
    pub fn faf8(&mut self) -> Faf8W<FafifoSpec> {
        Faf8W::new(self, 8)
    }
    #[doc = "Bit 9 - Filter 9 associated with FIFO"]
    #[inline(always)]
    #[must_use]
    pub fn faf9(&mut self) -> Faf9W<FafifoSpec> {
        Faf9W::new(self, 9)
    }
    #[doc = "Bit 10 - Filter 10 associated with FIFO"]
    #[inline(always)]
    #[must_use]
    pub fn faf10(&mut self) -> Faf10W<FafifoSpec> {
        Faf10W::new(self, 10)
    }
    #[doc = "Bit 11 - Filter 11 associated with FIFO"]
    #[inline(always)]
    #[must_use]
    pub fn faf11(&mut self) -> Faf11W<FafifoSpec> {
        Faf11W::new(self, 11)
    }
    #[doc = "Bit 12 - Filter 12 associated with FIFO"]
    #[inline(always)]
    #[must_use]
    pub fn faf12(&mut self) -> Faf12W<FafifoSpec> {
        Faf12W::new(self, 12)
    }
    #[doc = "Bit 13 - Filter 13 associated with FIFO"]
    #[inline(always)]
    #[must_use]
    pub fn faf13(&mut self) -> Faf13W<FafifoSpec> {
        Faf13W::new(self, 13)
    }
}
#[doc = "Filter associated FIFO register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`fafifo::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`fafifo::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct FafifoSpec;
impl crate::RegisterSpec for FafifoSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`fafifo::R`](R) reader structure"]
impl crate::Readable for FafifoSpec {}
#[doc = "`write(|w| ..)` method takes [`fafifo::W`](W) writer structure"]
impl crate::Writable for FafifoSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets FAFIFO to value 0"]
impl crate::Resettable for FafifoSpec {
    const RESET_VALUE: u32 = 0;
}
