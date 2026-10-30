#[doc = "Register `ST3CAP1TRG` reader"]
pub type R = crate::R<St3cap1trgSpec>;
#[doc = "Register `ST3CAP1TRG` writer"]
pub type W = crate::W<St3cap1trgSpec>;
#[doc = "Field `CP1BSW` reader - Capture 1 triggered by software"]
pub type Cp1bswR = crate::BitReader;
#[doc = "Field `CP1BSW` writer - Capture 1 triggered by software"]
pub type Cp1bswW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CP1BUP` reader - Capture 1 triggered by update event"]
pub type Cp1bupR = crate::BitReader;
#[doc = "Field `CP1BUP` writer - Capture 1 triggered by update event"]
pub type Cp1bupW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CP1BEXEV0` reader - Capture 1 triggered by external event 0"]
pub type Cp1bexev0R = crate::BitReader;
#[doc = "Field `CP1BEXEV0` writer - Capture 1 triggered by external event 0"]
pub type Cp1bexev0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CP1BEXEV1` reader - Capture 1 triggered by external event 1"]
pub type Cp1bexev1R = crate::BitReader;
#[doc = "Field `CP1BEXEV1` writer - Capture 1 triggered by external event 1"]
pub type Cp1bexev1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CP1BEXEV2` reader - Capture 1 triggered by external event 2"]
pub type Cp1bexev2R = crate::BitReader;
#[doc = "Field `CP1BEXEV2` writer - Capture 1 triggered by external event 2"]
pub type Cp1bexev2W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CP1BEXEV3` reader - Capture 1 triggered by external event 3"]
pub type Cp1bexev3R = crate::BitReader;
#[doc = "Field `CP1BEXEV3` writer - Capture 1 triggered by external event 3"]
pub type Cp1bexev3W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CP1BEXEV4` reader - Capture 1 triggered by external event 4"]
pub type Cp1bexev4R = crate::BitReader;
#[doc = "Field `CP1BEXEV4` writer - Capture 1 triggered by external event 4"]
pub type Cp1bexev4W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CP1BEXEV5` reader - Capture 1 triggered by external event 5"]
pub type Cp1bexev5R = crate::BitReader;
#[doc = "Field `CP1BEXEV5` writer - Capture 1 triggered by external event 5"]
pub type Cp1bexev5W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CP1BEXEV6` reader - Capture 1 triggered by external event 6"]
pub type Cp1bexev6R = crate::BitReader;
#[doc = "Field `CP1BEXEV6` writer - Capture 1 triggered by external event 6"]
pub type Cp1bexev6W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CP1BEXEV7` reader - Capture 1 triggered by external event 7"]
pub type Cp1bexev7R = crate::BitReader;
#[doc = "Field `CP1BEXEV7` writer - Capture 1 triggered by external event 7"]
pub type Cp1bexev7W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CP1BEXEV8` reader - Capture 1 triggered by external event 8"]
pub type Cp1bexev8R = crate::BitReader;
#[doc = "Field `CP1BEXEV8` writer - Capture 1 triggered by external event 8"]
pub type Cp1bexev8W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CP1BEXEV9` reader - Capture 1 triggered by external event 9"]
pub type Cp1bexev9R = crate::BitReader;
#[doc = "Field `CP1BEXEV9` writer - Capture 1 triggered by external event 9"]
pub type Cp1bexev9W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CP1BST3A` reader - Capture 1 triggered by ST3CH0_O output inactive to active transition"]
pub type Cp1bst3aR = crate::BitReader;
#[doc = "Field `CP1BST3A` writer - Capture 1 triggered by ST3CH0_O output inactive to active transition"]
pub type Cp1bst3aW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CP1BST3NA` reader - Capture 1 triggered by ST3CH0_O output active to inactive transition"]
pub type Cp1bst3naR = crate::BitReader;
#[doc = "Field `CP1BST3NA` writer - Capture 1 triggered by ST3CH0_O output active to inactive transition"]
pub type Cp1bst3naW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CP1BST3CMP0` reader - Capture 1 triggered by compare 0 event of Slave_TIMER3"]
pub type Cp1bst3cmp0R = crate::BitReader;
#[doc = "Field `CP1BST3CMP0` writer - Capture 1 triggered by compare 0 event of Slave_TIMER3"]
pub type Cp1bst3cmp0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CP1BST3CMP1` reader - Capture 1 triggered by compare 1 event of Slave_TIMER3"]
pub type Cp1bst3cmp1R = crate::BitReader;
#[doc = "Field `CP1BST3CMP1` writer - Capture 1 triggered by compare 1 event of Slave_TIMER3"]
pub type Cp1bst3cmp1W<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Capture 1 triggered by software"]
    #[inline(always)]
    pub fn cp1bsw(&self) -> Cp1bswR {
        Cp1bswR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Capture 1 triggered by update event"]
    #[inline(always)]
    pub fn cp1bup(&self) -> Cp1bupR {
        Cp1bupR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Capture 1 triggered by external event 0"]
    #[inline(always)]
    pub fn cp1bexev0(&self) -> Cp1bexev0R {
        Cp1bexev0R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Capture 1 triggered by external event 1"]
    #[inline(always)]
    pub fn cp1bexev1(&self) -> Cp1bexev1R {
        Cp1bexev1R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Capture 1 triggered by external event 2"]
    #[inline(always)]
    pub fn cp1bexev2(&self) -> Cp1bexev2R {
        Cp1bexev2R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Capture 1 triggered by external event 3"]
    #[inline(always)]
    pub fn cp1bexev3(&self) -> Cp1bexev3R {
        Cp1bexev3R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Capture 1 triggered by external event 4"]
    #[inline(always)]
    pub fn cp1bexev4(&self) -> Cp1bexev4R {
        Cp1bexev4R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Capture 1 triggered by external event 5"]
    #[inline(always)]
    pub fn cp1bexev5(&self) -> Cp1bexev5R {
        Cp1bexev5R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Capture 1 triggered by external event 6"]
    #[inline(always)]
    pub fn cp1bexev6(&self) -> Cp1bexev6R {
        Cp1bexev6R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Capture 1 triggered by external event 7"]
    #[inline(always)]
    pub fn cp1bexev7(&self) -> Cp1bexev7R {
        Cp1bexev7R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Capture 1 triggered by external event 8"]
    #[inline(always)]
    pub fn cp1bexev8(&self) -> Cp1bexev8R {
        Cp1bexev8R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Capture 1 triggered by external event 9"]
    #[inline(always)]
    pub fn cp1bexev9(&self) -> Cp1bexev9R {
        Cp1bexev9R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 24 - Capture 1 triggered by ST3CH0_O output inactive to active transition"]
    #[inline(always)]
    pub fn cp1bst3a(&self) -> Cp1bst3aR {
        Cp1bst3aR::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - Capture 1 triggered by ST3CH0_O output active to inactive transition"]
    #[inline(always)]
    pub fn cp1bst3na(&self) -> Cp1bst3naR {
        Cp1bst3naR::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - Capture 1 triggered by compare 0 event of Slave_TIMER3"]
    #[inline(always)]
    pub fn cp1bst3cmp0(&self) -> Cp1bst3cmp0R {
        Cp1bst3cmp0R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - Capture 1 triggered by compare 1 event of Slave_TIMER3"]
    #[inline(always)]
    pub fn cp1bst3cmp1(&self) -> Cp1bst3cmp1R {
        Cp1bst3cmp1R::new(((self.bits >> 27) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Capture 1 triggered by software"]
    #[inline(always)]
    #[must_use]
    pub fn cp1bsw(&mut self) -> Cp1bswW<St3cap1trgSpec> {
        Cp1bswW::new(self, 0)
    }
    #[doc = "Bit 1 - Capture 1 triggered by update event"]
    #[inline(always)]
    #[must_use]
    pub fn cp1bup(&mut self) -> Cp1bupW<St3cap1trgSpec> {
        Cp1bupW::new(self, 1)
    }
    #[doc = "Bit 2 - Capture 1 triggered by external event 0"]
    #[inline(always)]
    #[must_use]
    pub fn cp1bexev0(&mut self) -> Cp1bexev0W<St3cap1trgSpec> {
        Cp1bexev0W::new(self, 2)
    }
    #[doc = "Bit 3 - Capture 1 triggered by external event 1"]
    #[inline(always)]
    #[must_use]
    pub fn cp1bexev1(&mut self) -> Cp1bexev1W<St3cap1trgSpec> {
        Cp1bexev1W::new(self, 3)
    }
    #[doc = "Bit 4 - Capture 1 triggered by external event 2"]
    #[inline(always)]
    #[must_use]
    pub fn cp1bexev2(&mut self) -> Cp1bexev2W<St3cap1trgSpec> {
        Cp1bexev2W::new(self, 4)
    }
    #[doc = "Bit 5 - Capture 1 triggered by external event 3"]
    #[inline(always)]
    #[must_use]
    pub fn cp1bexev3(&mut self) -> Cp1bexev3W<St3cap1trgSpec> {
        Cp1bexev3W::new(self, 5)
    }
    #[doc = "Bit 6 - Capture 1 triggered by external event 4"]
    #[inline(always)]
    #[must_use]
    pub fn cp1bexev4(&mut self) -> Cp1bexev4W<St3cap1trgSpec> {
        Cp1bexev4W::new(self, 6)
    }
    #[doc = "Bit 7 - Capture 1 triggered by external event 5"]
    #[inline(always)]
    #[must_use]
    pub fn cp1bexev5(&mut self) -> Cp1bexev5W<St3cap1trgSpec> {
        Cp1bexev5W::new(self, 7)
    }
    #[doc = "Bit 8 - Capture 1 triggered by external event 6"]
    #[inline(always)]
    #[must_use]
    pub fn cp1bexev6(&mut self) -> Cp1bexev6W<St3cap1trgSpec> {
        Cp1bexev6W::new(self, 8)
    }
    #[doc = "Bit 9 - Capture 1 triggered by external event 7"]
    #[inline(always)]
    #[must_use]
    pub fn cp1bexev7(&mut self) -> Cp1bexev7W<St3cap1trgSpec> {
        Cp1bexev7W::new(self, 9)
    }
    #[doc = "Bit 10 - Capture 1 triggered by external event 8"]
    #[inline(always)]
    #[must_use]
    pub fn cp1bexev8(&mut self) -> Cp1bexev8W<St3cap1trgSpec> {
        Cp1bexev8W::new(self, 10)
    }
    #[doc = "Bit 11 - Capture 1 triggered by external event 9"]
    #[inline(always)]
    #[must_use]
    pub fn cp1bexev9(&mut self) -> Cp1bexev9W<St3cap1trgSpec> {
        Cp1bexev9W::new(self, 11)
    }
    #[doc = "Bit 24 - Capture 1 triggered by ST3CH0_O output inactive to active transition"]
    #[inline(always)]
    #[must_use]
    pub fn cp1bst3a(&mut self) -> Cp1bst3aW<St3cap1trgSpec> {
        Cp1bst3aW::new(self, 24)
    }
    #[doc = "Bit 25 - Capture 1 triggered by ST3CH0_O output active to inactive transition"]
    #[inline(always)]
    #[must_use]
    pub fn cp1bst3na(&mut self) -> Cp1bst3naW<St3cap1trgSpec> {
        Cp1bst3naW::new(self, 25)
    }
    #[doc = "Bit 26 - Capture 1 triggered by compare 0 event of Slave_TIMER3"]
    #[inline(always)]
    #[must_use]
    pub fn cp1bst3cmp0(&mut self) -> Cp1bst3cmp0W<St3cap1trgSpec> {
        Cp1bst3cmp0W::new(self, 26)
    }
    #[doc = "Bit 27 - Capture 1 triggered by compare 1 event of Slave_TIMER3"]
    #[inline(always)]
    #[must_use]
    pub fn cp1bst3cmp1(&mut self) -> Cp1bst3cmp1W<St3cap1trgSpec> {
        Cp1bst3cmp1W::new(self, 27)
    }
}
#[doc = "SHRTIMER Slave_TIMERx capture 1 trigger register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st3cap1trg::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st3cap1trg::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct St3cap1trgSpec;
impl crate::RegisterSpec for St3cap1trgSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`st3cap1trg::R`](R) reader structure"]
impl crate::Readable for St3cap1trgSpec {}
#[doc = "`write(|w| ..)` method takes [`st3cap1trg::W`](W) writer structure"]
impl crate::Writable for St3cap1trgSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets ST3CAP1TRG to value 0"]
impl crate::Resettable for St3cap1trgSpec {
    const RESET_VALUE: u32 = 0;
}
