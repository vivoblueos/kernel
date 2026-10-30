#[doc = "Register `FSCFG` reader"]
pub type R = crate::R<FscfgSpec>;
#[doc = "Register `FSCFG` writer"]
pub type W = crate::W<FscfgSpec>;
#[doc = "Field `FS0` reader - Filter scale configuration"]
pub type Fs0R = crate::BitReader;
#[doc = "Field `FS0` writer - Filter scale configuration"]
pub type Fs0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FS1` reader - Filter scale configuration"]
pub type Fs1R = crate::BitReader;
#[doc = "Field `FS1` writer - Filter scale configuration"]
pub type Fs1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FS2` reader - Filter scale configuration"]
pub type Fs2R = crate::BitReader;
#[doc = "Field `FS2` writer - Filter scale configuration"]
pub type Fs2W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FS3` reader - Filter scale configuration"]
pub type Fs3R = crate::BitReader;
#[doc = "Field `FS3` writer - Filter scale configuration"]
pub type Fs3W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FS4` reader - Filter scale configuration"]
pub type Fs4R = crate::BitReader;
#[doc = "Field `FS4` writer - Filter scale configuration"]
pub type Fs4W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FS5` reader - Filter scale configuration"]
pub type Fs5R = crate::BitReader;
#[doc = "Field `FS5` writer - Filter scale configuration"]
pub type Fs5W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FS6` reader - Filter scale configuration"]
pub type Fs6R = crate::BitReader;
#[doc = "Field `FS6` writer - Filter scale configuration"]
pub type Fs6W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FS7` reader - Filter scale configuration"]
pub type Fs7R = crate::BitReader;
#[doc = "Field `FS7` writer - Filter scale configuration"]
pub type Fs7W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FS8` reader - Filter scale configuration"]
pub type Fs8R = crate::BitReader;
#[doc = "Field `FS8` writer - Filter scale configuration"]
pub type Fs8W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FS9` reader - Filter scale configuration"]
pub type Fs9R = crate::BitReader;
#[doc = "Field `FS9` writer - Filter scale configuration"]
pub type Fs9W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FS10` reader - Filter scale configuration"]
pub type Fs10R = crate::BitReader;
#[doc = "Field `FS10` writer - Filter scale configuration"]
pub type Fs10W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FS11` reader - Filter scale configuration"]
pub type Fs11R = crate::BitReader;
#[doc = "Field `FS11` writer - Filter scale configuration"]
pub type Fs11W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FS12` reader - Filter scale configuration"]
pub type Fs12R = crate::BitReader;
#[doc = "Field `FS12` writer - Filter scale configuration"]
pub type Fs12W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `FS13` reader - Filter scale configuration"]
pub type Fs13R = crate::BitReader;
#[doc = "Field `FS13` writer - Filter scale configuration"]
pub type Fs13W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Filter scale configuration"]
    #[inline(always)]
    pub fn fs0(&self) -> Fs0R {
        Fs0R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Filter scale configuration"]
    #[inline(always)]
    pub fn fs1(&self) -> Fs1R {
        Fs1R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Filter scale configuration"]
    #[inline(always)]
    pub fn fs2(&self) -> Fs2R {
        Fs2R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Filter scale configuration"]
    #[inline(always)]
    pub fn fs3(&self) -> Fs3R {
        Fs3R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Filter scale configuration"]
    #[inline(always)]
    pub fn fs4(&self) -> Fs4R {
        Fs4R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Filter scale configuration"]
    #[inline(always)]
    pub fn fs5(&self) -> Fs5R {
        Fs5R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Filter scale configuration"]
    #[inline(always)]
    pub fn fs6(&self) -> Fs6R {
        Fs6R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Filter scale configuration"]
    #[inline(always)]
    pub fn fs7(&self) -> Fs7R {
        Fs7R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Filter scale configuration"]
    #[inline(always)]
    pub fn fs8(&self) -> Fs8R {
        Fs8R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Filter scale configuration"]
    #[inline(always)]
    pub fn fs9(&self) -> Fs9R {
        Fs9R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Filter scale configuration"]
    #[inline(always)]
    pub fn fs10(&self) -> Fs10R {
        Fs10R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Filter scale configuration"]
    #[inline(always)]
    pub fn fs11(&self) -> Fs11R {
        Fs11R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Filter scale configuration"]
    #[inline(always)]
    pub fn fs12(&self) -> Fs12R {
        Fs12R::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Filter scale configuration"]
    #[inline(always)]
    pub fn fs13(&self) -> Fs13R {
        Fs13R::new(((self.bits >> 13) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Filter scale configuration"]
    #[inline(always)]
    #[must_use]
    pub fn fs0(&mut self) -> Fs0W<FscfgSpec> {
        Fs0W::new(self, 0)
    }
    #[doc = "Bit 1 - Filter scale configuration"]
    #[inline(always)]
    #[must_use]
    pub fn fs1(&mut self) -> Fs1W<FscfgSpec> {
        Fs1W::new(self, 1)
    }
    #[doc = "Bit 2 - Filter scale configuration"]
    #[inline(always)]
    #[must_use]
    pub fn fs2(&mut self) -> Fs2W<FscfgSpec> {
        Fs2W::new(self, 2)
    }
    #[doc = "Bit 3 - Filter scale configuration"]
    #[inline(always)]
    #[must_use]
    pub fn fs3(&mut self) -> Fs3W<FscfgSpec> {
        Fs3W::new(self, 3)
    }
    #[doc = "Bit 4 - Filter scale configuration"]
    #[inline(always)]
    #[must_use]
    pub fn fs4(&mut self) -> Fs4W<FscfgSpec> {
        Fs4W::new(self, 4)
    }
    #[doc = "Bit 5 - Filter scale configuration"]
    #[inline(always)]
    #[must_use]
    pub fn fs5(&mut self) -> Fs5W<FscfgSpec> {
        Fs5W::new(self, 5)
    }
    #[doc = "Bit 6 - Filter scale configuration"]
    #[inline(always)]
    #[must_use]
    pub fn fs6(&mut self) -> Fs6W<FscfgSpec> {
        Fs6W::new(self, 6)
    }
    #[doc = "Bit 7 - Filter scale configuration"]
    #[inline(always)]
    #[must_use]
    pub fn fs7(&mut self) -> Fs7W<FscfgSpec> {
        Fs7W::new(self, 7)
    }
    #[doc = "Bit 8 - Filter scale configuration"]
    #[inline(always)]
    #[must_use]
    pub fn fs8(&mut self) -> Fs8W<FscfgSpec> {
        Fs8W::new(self, 8)
    }
    #[doc = "Bit 9 - Filter scale configuration"]
    #[inline(always)]
    #[must_use]
    pub fn fs9(&mut self) -> Fs9W<FscfgSpec> {
        Fs9W::new(self, 9)
    }
    #[doc = "Bit 10 - Filter scale configuration"]
    #[inline(always)]
    #[must_use]
    pub fn fs10(&mut self) -> Fs10W<FscfgSpec> {
        Fs10W::new(self, 10)
    }
    #[doc = "Bit 11 - Filter scale configuration"]
    #[inline(always)]
    #[must_use]
    pub fn fs11(&mut self) -> Fs11W<FscfgSpec> {
        Fs11W::new(self, 11)
    }
    #[doc = "Bit 12 - Filter scale configuration"]
    #[inline(always)]
    #[must_use]
    pub fn fs12(&mut self) -> Fs12W<FscfgSpec> {
        Fs12W::new(self, 12)
    }
    #[doc = "Bit 13 - Filter scale configuration"]
    #[inline(always)]
    #[must_use]
    pub fn fs13(&mut self) -> Fs13W<FscfgSpec> {
        Fs13W::new(self, 13)
    }
}
#[doc = "Filter scale configuration register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`fscfg::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`fscfg::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct FscfgSpec;
impl crate::RegisterSpec for FscfgSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`fscfg::R`](R) reader structure"]
impl crate::Readable for FscfgSpec {}
#[doc = "`write(|w| ..)` method takes [`fscfg::W`](W) writer structure"]
impl crate::Writable for FscfgSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets FSCFG to value 0"]
impl crate::Resettable for FscfgSpec {
    const RESET_VALUE: u32 = 0;
}
