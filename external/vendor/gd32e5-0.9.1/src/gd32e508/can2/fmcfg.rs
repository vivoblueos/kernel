#[doc = "Register `FMCFG` reader"]
pub type R = crate::R<FmcfgSpec>;
#[doc = "Register `FMCFG` writer"]
pub type W = crate::W<FmcfgSpec>;
#[doc = "Field `FMOD0` reader - Filter mode"]
pub type Fmod0R = crate::BitReader;
#[doc = "Field `FMOD0` writer - Filter mode"]
pub type Fmod0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FMOD1` reader - Filter mode"]
pub type Fmod1R = crate::BitReader;
#[doc = "Field `FMOD1` writer - Filter mode"]
pub type Fmod1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FMOD2` reader - Filter mode"]
pub type Fmod2R = crate::BitReader;
#[doc = "Field `FMOD2` writer - Filter mode"]
pub type Fmod2W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FMOD3` reader - Filter mode"]
pub type Fmod3R = crate::BitReader;
#[doc = "Field `FMOD3` writer - Filter mode"]
pub type Fmod3W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FMOD4` reader - Filter mode"]
pub type Fmod4R = crate::BitReader;
#[doc = "Field `FMOD4` writer - Filter mode"]
pub type Fmod4W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FMOD5` reader - Filter mode"]
pub type Fmod5R = crate::BitReader;
#[doc = "Field `FMOD5` writer - Filter mode"]
pub type Fmod5W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FMOD6` reader - Filter mode"]
pub type Fmod6R = crate::BitReader;
#[doc = "Field `FMOD6` writer - Filter mode"]
pub type Fmod6W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FMOD7` reader - Filter mode"]
pub type Fmod7R = crate::BitReader;
#[doc = "Field `FMOD7` writer - Filter mode"]
pub type Fmod7W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FMOD8` reader - Filter mode"]
pub type Fmod8R = crate::BitReader;
#[doc = "Field `FMOD8` writer - Filter mode"]
pub type Fmod8W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FMOD9` reader - Filter mode"]
pub type Fmod9R = crate::BitReader;
#[doc = "Field `FMOD9` writer - Filter mode"]
pub type Fmod9W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FMOD10` reader - Filter mode"]
pub type Fmod10R = crate::BitReader;
#[doc = "Field `FMOD10` writer - Filter mode"]
pub type Fmod10W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FMOD11` reader - Filter mode"]
pub type Fmod11R = crate::BitReader;
#[doc = "Field `FMOD11` writer - Filter mode"]
pub type Fmod11W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FMOD12` reader - Filter mode"]
pub type Fmod12R = crate::BitReader;
#[doc = "Field `FMOD12` writer - Filter mode"]
pub type Fmod12W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FMOD13` reader - Filter mode"]
pub type Fmod13R = crate::BitReader;
#[doc = "Field `FMOD13` writer - Filter mode"]
pub type Fmod13W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Filter mode"]
    #[inline(always)]
    pub fn fmod0(&self) -> Fmod0R {
        Fmod0R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Filter mode"]
    #[inline(always)]
    pub fn fmod1(&self) -> Fmod1R {
        Fmod1R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Filter mode"]
    #[inline(always)]
    pub fn fmod2(&self) -> Fmod2R {
        Fmod2R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Filter mode"]
    #[inline(always)]
    pub fn fmod3(&self) -> Fmod3R {
        Fmod3R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Filter mode"]
    #[inline(always)]
    pub fn fmod4(&self) -> Fmod4R {
        Fmod4R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Filter mode"]
    #[inline(always)]
    pub fn fmod5(&self) -> Fmod5R {
        Fmod5R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Filter mode"]
    #[inline(always)]
    pub fn fmod6(&self) -> Fmod6R {
        Fmod6R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Filter mode"]
    #[inline(always)]
    pub fn fmod7(&self) -> Fmod7R {
        Fmod7R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Filter mode"]
    #[inline(always)]
    pub fn fmod8(&self) -> Fmod8R {
        Fmod8R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Filter mode"]
    #[inline(always)]
    pub fn fmod9(&self) -> Fmod9R {
        Fmod9R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Filter mode"]
    #[inline(always)]
    pub fn fmod10(&self) -> Fmod10R {
        Fmod10R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Filter mode"]
    #[inline(always)]
    pub fn fmod11(&self) -> Fmod11R {
        Fmod11R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Filter mode"]
    #[inline(always)]
    pub fn fmod12(&self) -> Fmod12R {
        Fmod12R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Filter mode"]
    #[inline(always)]
    pub fn fmod13(&self) -> Fmod13R {
        Fmod13R::new(((self.bits >> 13) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Filter mode"]
    #[inline(always)]
    #[must_use]
    pub fn fmod0(&mut self) -> Fmod0W<FmcfgSpec> {
        Fmod0W::new(self, 0)
    }
    #[doc = "Bit 1 - Filter mode"]
    #[inline(always)]
    #[must_use]
    pub fn fmod1(&mut self) -> Fmod1W<FmcfgSpec> {
        Fmod1W::new(self, 1)
    }
    #[doc = "Bit 2 - Filter mode"]
    #[inline(always)]
    #[must_use]
    pub fn fmod2(&mut self) -> Fmod2W<FmcfgSpec> {
        Fmod2W::new(self, 2)
    }
    #[doc = "Bit 3 - Filter mode"]
    #[inline(always)]
    #[must_use]
    pub fn fmod3(&mut self) -> Fmod3W<FmcfgSpec> {
        Fmod3W::new(self, 3)
    }
    #[doc = "Bit 4 - Filter mode"]
    #[inline(always)]
    #[must_use]
    pub fn fmod4(&mut self) -> Fmod4W<FmcfgSpec> {
        Fmod4W::new(self, 4)
    }
    #[doc = "Bit 5 - Filter mode"]
    #[inline(always)]
    #[must_use]
    pub fn fmod5(&mut self) -> Fmod5W<FmcfgSpec> {
        Fmod5W::new(self, 5)
    }
    #[doc = "Bit 6 - Filter mode"]
    #[inline(always)]
    #[must_use]
    pub fn fmod6(&mut self) -> Fmod6W<FmcfgSpec> {
        Fmod6W::new(self, 6)
    }
    #[doc = "Bit 7 - Filter mode"]
    #[inline(always)]
    #[must_use]
    pub fn fmod7(&mut self) -> Fmod7W<FmcfgSpec> {
        Fmod7W::new(self, 7)
    }
    #[doc = "Bit 8 - Filter mode"]
    #[inline(always)]
    #[must_use]
    pub fn fmod8(&mut self) -> Fmod8W<FmcfgSpec> {
        Fmod8W::new(self, 8)
    }
    #[doc = "Bit 9 - Filter mode"]
    #[inline(always)]
    #[must_use]
    pub fn fmod9(&mut self) -> Fmod9W<FmcfgSpec> {
        Fmod9W::new(self, 9)
    }
    #[doc = "Bit 10 - Filter mode"]
    #[inline(always)]
    #[must_use]
    pub fn fmod10(&mut self) -> Fmod10W<FmcfgSpec> {
        Fmod10W::new(self, 10)
    }
    #[doc = "Bit 11 - Filter mode"]
    #[inline(always)]
    #[must_use]
    pub fn fmod11(&mut self) -> Fmod11W<FmcfgSpec> {
        Fmod11W::new(self, 11)
    }
    #[doc = "Bit 12 - Filter mode"]
    #[inline(always)]
    #[must_use]
    pub fn fmod12(&mut self) -> Fmod12W<FmcfgSpec> {
        Fmod12W::new(self, 12)
    }
    #[doc = "Bit 13 - Filter mode"]
    #[inline(always)]
    #[must_use]
    pub fn fmod13(&mut self) -> Fmod13W<FmcfgSpec> {
        Fmod13W::new(self, 13)
    }
}
#[doc = "Filter mode configuration register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`fmcfg::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`fmcfg::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct FmcfgSpec;
impl crate::RegisterSpec for FmcfgSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`fmcfg::R`](R) reader structure"]
impl crate::Readable for FmcfgSpec {}
#[doc = "`write(|w| ..)` method takes [`fmcfg::W`](W) writer structure"]
impl crate::Writable for FmcfgSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets FMCFG to value 0"]
impl crate::Resettable for FmcfgSpec {
    const RESET_VALUE: u32 = 0;
}
