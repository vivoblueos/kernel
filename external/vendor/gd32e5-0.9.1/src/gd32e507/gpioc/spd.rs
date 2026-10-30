#[doc = "Register `SPD` reader"]
pub type R = crate::R<SpdSpec>;
#[doc = "Register `SPD` writer"]
pub type W = crate::W<SpdSpec>;
#[doc = "Field `SPD0` reader - Port 0 output max speed bits"]
pub type Spd0R = crate::BitReader;
#[doc = "Field `SPD0` writer - Port 0 output max speed bits"]
pub type Spd0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPD1` reader - Port 1 output max speed bits"]
pub type Spd1R = crate::BitReader;
#[doc = "Field `SPD1` writer - Port 1 output max speed bits"]
pub type Spd1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPD2` reader - Port 2 output max speed bits"]
pub type Spd2R = crate::BitReader;
#[doc = "Field `SPD2` writer - Port 2 output max speed bits"]
pub type Spd2W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPD3` reader - Port 3 output max speed bits"]
pub type Spd3R = crate::BitReader;
#[doc = "Field `SPD3` writer - Port 3 output max speed bits"]
pub type Spd3W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPD4` reader - Port 4 output max speed bits"]
pub type Spd4R = crate::BitReader;
#[doc = "Field `SPD4` writer - Port 4 output max speed bits"]
pub type Spd4W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPD5` reader - Port 5 output max speed bits"]
pub type Spd5R = crate::BitReader;
#[doc = "Field `SPD5` writer - Port 5 output max speed bits"]
pub type Spd5W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPD6` reader - Port 6 output max speed bits"]
pub type Spd6R = crate::BitReader;
#[doc = "Field `SPD6` writer - Port 6 output max speed bits"]
pub type Spd6W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPD7` reader - Port 7 output max speed bits"]
pub type Spd7R = crate::BitReader;
#[doc = "Field `SPD7` writer - Port 7 output max speed bits"]
pub type Spd7W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPD8` reader - Port 8 output max speed bits"]
pub type Spd8R = crate::BitReader;
#[doc = "Field `SPD8` writer - Port 8 output max speed bits"]
pub type Spd8W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPD9` reader - Port 9 output max speed bits"]
pub type Spd9R = crate::BitReader;
#[doc = "Field `SPD9` writer - Port 9 output max speed bits"]
pub type Spd9W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPD10` reader - Port 10 output max speed bits"]
pub type Spd10R = crate::BitReader;
#[doc = "Field `SPD10` writer - Port 10 output max speed bits"]
pub type Spd10W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPD11` reader - Port 11 output max speed bits"]
pub type Spd11R = crate::BitReader;
#[doc = "Field `SPD11` writer - Port 11 output max speed bits"]
pub type Spd11W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPD12` reader - Port 12 output max speed bits"]
pub type Spd12R = crate::BitReader;
#[doc = "Field `SPD12` writer - Port 12 output max speed bits"]
pub type Spd12W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPD13` reader - Port 13 output max speed bits"]
pub type Spd13R = crate::BitReader;
#[doc = "Field `SPD13` writer - Port 13 output max speed bits"]
pub type Spd13W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPD14` reader - Port 14 output max speed bits"]
pub type Spd14R = crate::BitReader;
#[doc = "Field `SPD14` writer - Port 14 output max speed bits"]
pub type Spd14W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPD15` reader - Port 15 output max speed bits"]
pub type Spd15R = crate::BitReader;
#[doc = "Field `SPD15` writer - Port 15 output max speed bits"]
pub type Spd15W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Port 0 output max speed bits"]
    #[inline(always)]
    pub fn spd0(&self) -> Spd0R {
        Spd0R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Port 1 output max speed bits"]
    #[inline(always)]
    pub fn spd1(&self) -> Spd1R {
        Spd1R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Port 2 output max speed bits"]
    #[inline(always)]
    pub fn spd2(&self) -> Spd2R {
        Spd2R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Port 3 output max speed bits"]
    #[inline(always)]
    pub fn spd3(&self) -> Spd3R {
        Spd3R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Port 4 output max speed bits"]
    #[inline(always)]
    pub fn spd4(&self) -> Spd4R {
        Spd4R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Port 5 output max speed bits"]
    #[inline(always)]
    pub fn spd5(&self) -> Spd5R {
        Spd5R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Port 6 output max speed bits"]
    #[inline(always)]
    pub fn spd6(&self) -> Spd6R {
        Spd6R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Port 7 output max speed bits"]
    #[inline(always)]
    pub fn spd7(&self) -> Spd7R {
        Spd7R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Port 8 output max speed bits"]
    #[inline(always)]
    pub fn spd8(&self) -> Spd8R {
        Spd8R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Port 9 output max speed bits"]
    #[inline(always)]
    pub fn spd9(&self) -> Spd9R {
        Spd9R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Port 10 output max speed bits"]
    #[inline(always)]
    pub fn spd10(&self) -> Spd10R {
        Spd10R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Port 11 output max speed bits"]
    #[inline(always)]
    pub fn spd11(&self) -> Spd11R {
        Spd11R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Port 12 output max speed bits"]
    #[inline(always)]
    pub fn spd12(&self) -> Spd12R {
        Spd12R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Port 13 output max speed bits"]
    #[inline(always)]
    pub fn spd13(&self) -> Spd13R {
        Spd13R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Port 14 output max speed bits"]
    #[inline(always)]
    pub fn spd14(&self) -> Spd14R {
        Spd14R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Port 15 output max speed bits"]
    #[inline(always)]
    pub fn spd15(&self) -> Spd15R {
        Spd15R::new(((self.bits >> 15) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Port 0 output max speed bits"]
    #[inline(always)]
    #[must_use]
    pub fn spd0(&mut self) -> Spd0W<SpdSpec> {
        Spd0W::new(self, 0)
    }
    #[doc = "Bit 1 - Port 1 output max speed bits"]
    #[inline(always)]
    #[must_use]
    pub fn spd1(&mut self) -> Spd1W<SpdSpec> {
        Spd1W::new(self, 1)
    }
    #[doc = "Bit 2 - Port 2 output max speed bits"]
    #[inline(always)]
    #[must_use]
    pub fn spd2(&mut self) -> Spd2W<SpdSpec> {
        Spd2W::new(self, 2)
    }
    #[doc = "Bit 3 - Port 3 output max speed bits"]
    #[inline(always)]
    #[must_use]
    pub fn spd3(&mut self) -> Spd3W<SpdSpec> {
        Spd3W::new(self, 3)
    }
    #[doc = "Bit 4 - Port 4 output max speed bits"]
    #[inline(always)]
    #[must_use]
    pub fn spd4(&mut self) -> Spd4W<SpdSpec> {
        Spd4W::new(self, 4)
    }
    #[doc = "Bit 5 - Port 5 output max speed bits"]
    #[inline(always)]
    #[must_use]
    pub fn spd5(&mut self) -> Spd5W<SpdSpec> {
        Spd5W::new(self, 5)
    }
    #[doc = "Bit 6 - Port 6 output max speed bits"]
    #[inline(always)]
    #[must_use]
    pub fn spd6(&mut self) -> Spd6W<SpdSpec> {
        Spd6W::new(self, 6)
    }
    #[doc = "Bit 7 - Port 7 output max speed bits"]
    #[inline(always)]
    #[must_use]
    pub fn spd7(&mut self) -> Spd7W<SpdSpec> {
        Spd7W::new(self, 7)
    }
    #[doc = "Bit 8 - Port 8 output max speed bits"]
    #[inline(always)]
    #[must_use]
    pub fn spd8(&mut self) -> Spd8W<SpdSpec> {
        Spd8W::new(self, 8)
    }
    #[doc = "Bit 9 - Port 9 output max speed bits"]
    #[inline(always)]
    #[must_use]
    pub fn spd9(&mut self) -> Spd9W<SpdSpec> {
        Spd9W::new(self, 9)
    }
    #[doc = "Bit 10 - Port 10 output max speed bits"]
    #[inline(always)]
    #[must_use]
    pub fn spd10(&mut self) -> Spd10W<SpdSpec> {
        Spd10W::new(self, 10)
    }
    #[doc = "Bit 11 - Port 11 output max speed bits"]
    #[inline(always)]
    #[must_use]
    pub fn spd11(&mut self) -> Spd11W<SpdSpec> {
        Spd11W::new(self, 11)
    }
    #[doc = "Bit 12 - Port 12 output max speed bits"]
    #[inline(always)]
    #[must_use]
    pub fn spd12(&mut self) -> Spd12W<SpdSpec> {
        Spd12W::new(self, 12)
    }
    #[doc = "Bit 13 - Port 13 output max speed bits"]
    #[inline(always)]
    #[must_use]
    pub fn spd13(&mut self) -> Spd13W<SpdSpec> {
        Spd13W::new(self, 13)
    }
    #[doc = "Bit 14 - Port 14 output max speed bits"]
    #[inline(always)]
    #[must_use]
    pub fn spd14(&mut self) -> Spd14W<SpdSpec> {
        Spd14W::new(self, 14)
    }
    #[doc = "Bit 15 - Port 15 output max speed bits"]
    #[inline(always)]
    #[must_use]
    pub fn spd15(&mut self) -> Spd15W<SpdSpec> {
        Spd15W::new(self, 15)
    }
}
#[doc = "Port bit speed register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`spd::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`spd::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SpdSpec;
impl crate::RegisterSpec for SpdSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`spd::R`](R) reader structure"]
impl crate::Readable for SpdSpec {}
#[doc = "`write(|w| ..)` method takes [`spd::W`](W) writer structure"]
impl crate::Writable for SpdSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets SPD to value 0"]
impl crate::Resettable for SpdSpec {
    const RESET_VALUE: u32 = 0;
}
