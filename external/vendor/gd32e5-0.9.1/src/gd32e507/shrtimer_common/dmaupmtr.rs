#[doc = "Register `DMAUPMTR` reader"]
pub type R = crate::R<DmaupmtrSpec>;
#[doc = "Register `DMAUPMTR` writer"]
pub type W = crate::W<DmaupmtrSpec>;
#[doc = "Field `MTCTL0` reader - SHRTIMER_MTCTL0 update by DMA mode"]
pub type Mtctl0R = crate::BitReader;
#[doc = "Field `MTCTL0` writer - SHRTIMER_MTCTL0 update by DMA mode"]
pub type Mtctl0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTINTC` reader - SHRTIMER_MTINTC update by DMA mode"]
pub type MtintcR = crate::BitReader;
#[doc = "Field `MTINTC` writer - SHRTIMER_MTINTC update by DMA mode"]
pub type MtintcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTDMAINTEN` reader - SHRTIMER_MTDMAINTEN update by DMA mode"]
pub type MtdmaintenR = crate::BitReader;
#[doc = "Field `MTDMAINTEN` writer - SHRTIMER_MTDMAINTEN update by DMA mode"]
pub type MtdmaintenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTCNT` reader - SHRTIMER_MTCNT update by DMA mode"]
pub type MtcntR = crate::BitReader;
#[doc = "Field `MTCNT` writer - SHRTIMER_MTCNT update by DMA mode"]
pub type MtcntW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTCAR` reader - SHRTIMER_MTCAR update by DMA mode"]
pub type MtcarR = crate::BitReader;
#[doc = "Field `MTCAR` writer - SHRTIMER_MTCAR update by DMA mode"]
pub type MtcarW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTCREP` reader - SHRTIMER_MTCAR update by DMA mode"]
pub type MtcrepR = crate::BitReader;
#[doc = "Field `MTCREP` writer - SHRTIMER_MTCAR update by DMA mode"]
pub type MtcrepW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTCMP0V` reader - SHRTIMER_MTCMP0V update by DMA mode"]
pub type Mtcmp0vR = crate::BitReader;
#[doc = "Field `MTCMP0V` writer - SHRTIMER_MTCMP0V update by DMA mode"]
pub type Mtcmp0vW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTCMP1V` reader - SHRTIMER_MTCMP1V update by DMA mode"]
pub type Mtcmp1vR = crate::BitReader;
#[doc = "Field `MTCMP1V` writer - SHRTIMER_MTCMP1V update by DMA mode"]
pub type Mtcmp1vW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTCMP2V` reader - SHRTIMER_MTCMP2V update by DMA mode"]
pub type Mtcmp2vR = crate::BitReader;
#[doc = "Field `MTCMP2V` writer - SHRTIMER_MTCMP2V update by DMA mode"]
pub type Mtcmp2vW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTCMP3V` reader - SHRTIMER_MTCMP3V update by DMA mode"]
pub type Mtcmp3vR = crate::BitReader;
#[doc = "Field `MTCMP3V` writer - SHRTIMER_MTCMP3V update by DMA mode"]
pub type Mtcmp3vW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTACTL` reader - SHRTIMER_MTACTL update by DMA mode"]
pub type MtactlR = crate::BitReader;
#[doc = "Field `MTACTL` writer - SHRTIMER_MTACTL update by DMA mode"]
pub type MtactlW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - SHRTIMER_MTCTL0 update by DMA mode"]
    #[inline(always)]
    pub fn mtctl0(&self) -> Mtctl0R {
        Mtctl0R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - SHRTIMER_MTINTC update by DMA mode"]
    #[inline(always)]
    pub fn mtintc(&self) -> MtintcR {
        MtintcR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - SHRTIMER_MTDMAINTEN update by DMA mode"]
    #[inline(always)]
    pub fn mtdmainten(&self) -> MtdmaintenR {
        MtdmaintenR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - SHRTIMER_MTCNT update by DMA mode"]
    #[inline(always)]
    pub fn mtcnt(&self) -> MtcntR {
        MtcntR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - SHRTIMER_MTCAR update by DMA mode"]
    #[inline(always)]
    pub fn mtcar(&self) -> MtcarR {
        MtcarR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - SHRTIMER_MTCAR update by DMA mode"]
    #[inline(always)]
    pub fn mtcrep(&self) -> MtcrepR {
        MtcrepR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - SHRTIMER_MTCMP0V update by DMA mode"]
    #[inline(always)]
    pub fn mtcmp0v(&self) -> Mtcmp0vR {
        Mtcmp0vR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - SHRTIMER_MTCMP1V update by DMA mode"]
    #[inline(always)]
    pub fn mtcmp1v(&self) -> Mtcmp1vR {
        Mtcmp1vR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - SHRTIMER_MTCMP2V update by DMA mode"]
    #[inline(always)]
    pub fn mtcmp2v(&self) -> Mtcmp2vR {
        Mtcmp2vR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - SHRTIMER_MTCMP3V update by DMA mode"]
    #[inline(always)]
    pub fn mtcmp3v(&self) -> Mtcmp3vR {
        Mtcmp3vR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 31 - SHRTIMER_MTACTL update by DMA mode"]
    #[inline(always)]
    pub fn mtactl(&self) -> MtactlR {
        MtactlR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - SHRTIMER_MTCTL0 update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn mtctl0(&mut self) -> Mtctl0W<DmaupmtrSpec> {
        Mtctl0W::new(self, 0)
    }
    #[doc = "Bit 1 - SHRTIMER_MTINTC update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn mtintc(&mut self) -> MtintcW<DmaupmtrSpec> {
        MtintcW::new(self, 1)
    }
    #[doc = "Bit 2 - SHRTIMER_MTDMAINTEN update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn mtdmainten(&mut self) -> MtdmaintenW<DmaupmtrSpec> {
        MtdmaintenW::new(self, 2)
    }
    #[doc = "Bit 3 - SHRTIMER_MTCNT update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn mtcnt(&mut self) -> MtcntW<DmaupmtrSpec> {
        MtcntW::new(self, 3)
    }
    #[doc = "Bit 4 - SHRTIMER_MTCAR update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn mtcar(&mut self) -> MtcarW<DmaupmtrSpec> {
        MtcarW::new(self, 4)
    }
    #[doc = "Bit 5 - SHRTIMER_MTCAR update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn mtcrep(&mut self) -> MtcrepW<DmaupmtrSpec> {
        MtcrepW::new(self, 5)
    }
    #[doc = "Bit 6 - SHRTIMER_MTCMP0V update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn mtcmp0v(&mut self) -> Mtcmp0vW<DmaupmtrSpec> {
        Mtcmp0vW::new(self, 6)
    }
    #[doc = "Bit 7 - SHRTIMER_MTCMP1V update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn mtcmp1v(&mut self) -> Mtcmp1vW<DmaupmtrSpec> {
        Mtcmp1vW::new(self, 7)
    }
    #[doc = "Bit 8 - SHRTIMER_MTCMP2V update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn mtcmp2v(&mut self) -> Mtcmp2vW<DmaupmtrSpec> {
        Mtcmp2vW::new(self, 8)
    }
    #[doc = "Bit 9 - SHRTIMER_MTCMP3V update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn mtcmp3v(&mut self) -> Mtcmp3vW<DmaupmtrSpec> {
        Mtcmp3vW::new(self, 9)
    }
    #[doc = "Bit 31 - SHRTIMER_MTACTL update by DMA mode"]
    #[inline(always)]
    #[must_use]
    pub fn mtactl(&mut self) -> MtactlW<DmaupmtrSpec> {
        MtactlW::new(self, 31)
    }
}
#[doc = "SHRTIMER DMA update Master_TIMER register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`dmaupmtr::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`dmaupmtr::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DmaupmtrSpec;
impl crate::RegisterSpec for DmaupmtrSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`dmaupmtr::R`](R) reader structure"]
impl crate::Readable for DmaupmtrSpec {}
#[doc = "`write(|w| ..)` method takes [`dmaupmtr::W`](W) writer structure"]
impl crate::Writable for DmaupmtrSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DMAUPMTR to value 0"]
impl crate::Resettable for DmaupmtrSpec {
    const RESET_VALUE: u32 = 0;
}
