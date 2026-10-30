#[doc = "Register `BMSTRG` reader"]
pub type R = crate::R<BmstrgSpec>;
#[doc = "Register `BMSTRG` writer"]
pub type W = crate::W<BmstrgSpec>;
#[doc = "Field `SWTRG` reader - Software triggers bunch mode operation"]
pub type SwtrgR = crate::BitReader;
#[doc = "Field `SWTRG` writer - Software triggers bunch mode operation"]
pub type SwtrgW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTRST` reader - Master_TIMER reset event triggers bunch mode operation"]
pub type MtrstR = crate::BitReader;
#[doc = "Field `MTRST` writer - Master_TIMER reset event triggers bunch mode operation"]
pub type MtrstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTREP` reader - Master_TIMER repetition event triggers bunch mode operation"]
pub type MtrepR = crate::BitReader;
#[doc = "Field `MTREP` writer - Master_TIMER repetition event triggers bunch mode operation"]
pub type MtrepW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTCMP0` reader - Master_TIMER compare 0 event triggers bunch mode operation"]
pub type Mtcmp0R = crate::BitReader;
#[doc = "Field `MTCMP0` writer - Master_TIMER compare 0 event triggers bunch mode operation"]
pub type Mtcmp0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTCMP1` reader - Master_TIMER compare 1 event triggers bunch mode operation"]
pub type Mtcmp1R = crate::BitReader;
#[doc = "Field `MTCMP1` writer - Master_TIMER compare 1 event triggers bunch mode operation"]
pub type Mtcmp1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTCMP2` reader - Master_TIMER compare 2 event triggers bunch mode operation"]
pub type Mtcmp2R = crate::BitReader;
#[doc = "Field `MTCMP2` writer - Master_TIMER compare 2 event triggers bunch mode operation"]
pub type Mtcmp2W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTCMP3` reader - Master_TIMER compare 3 event triggers bunch mode operation"]
pub type Mtcmp3R = crate::BitReader;
#[doc = "Field `MTCMP3` writer - Master_TIMER compare 3 event triggers bunch mode operation"]
pub type Mtcmp3W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0RST` reader - Slave_TIMER0 reset event triggers bunch mode operation"]
pub type St0rstR = crate::BitReader;
#[doc = "Field `ST0RST` writer - Slave_TIMER0 reset event triggers bunch mode operation"]
pub type St0rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0REP` reader - Slave_TIMER0 repetition event triggers bunch mode operation"]
pub type St0repR = crate::BitReader;
#[doc = "Field `ST0REP` writer - Slave_TIMER0 repetition event triggers bunch mode operation"]
pub type St0repW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0CMP0` reader - Slave_TIMER0 compare 0 event triggers bunch mode operation"]
pub type St0cmp0R = crate::BitReader;
#[doc = "Field `ST0CMP0` writer - Slave_TIMER0 compare 0 event triggers bunch mode operation"]
pub type St0cmp0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0CMP1` reader - Slave_TIMER0 compare 1 event triggers bunch mode operation"]
pub type St0cmp1R = crate::BitReader;
#[doc = "Field `ST0CMP1` writer - Slave_TIMER0 compare 1 event triggers bunch mode operation"]
pub type St0cmp1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1RST` reader - Slave_TIMER1 reset event triggers bunch mode operation"]
pub type St1rstR = crate::BitReader;
#[doc = "Field `ST1RST` writer - Slave_TIMER1 reset event triggers bunch mode operation"]
pub type St1rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1REP` reader - Slave_TIMER1 repetition event triggers bunch mode operation"]
pub type St1repR = crate::BitReader;
#[doc = "Field `ST1REP` writer - Slave_TIMER1 repetition event triggers bunch mode operation"]
pub type St1repW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1CMP0` reader - Slave_TIMER1 compare 0 event triggers bunch mode operation"]
pub type St1cmp0R = crate::BitReader;
#[doc = "Field `ST1CMP0` writer - Slave_TIMER1 compare 0 event triggers bunch mode operation"]
pub type St1cmp0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1CMP1` reader - Slave_TIMER1 compare 1 event triggers bunch mode operation"]
pub type St1cmp1R = crate::BitReader;
#[doc = "Field `ST1CMP1` writer - Slave_TIMER1 compare 1 event triggers bunch mode operation"]
pub type St1cmp1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2RST` reader - Slave_TIMER2 reset event triggers bunch mode operation"]
pub type St2rstR = crate::BitReader;
#[doc = "Field `ST2RST` writer - Slave_TIMER2 reset event triggers bunch mode operation"]
pub type St2rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2REP` reader - Slave_TIMER1 repetition event triggers bunch mode operation"]
pub type St2repR = crate::BitReader;
#[doc = "Field `ST2REP` writer - Slave_TIMER1 repetition event triggers bunch mode operation"]
pub type St2repW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2CMP0` reader - Slave_TIMER2 compare 0 event triggers bunch mode operation"]
pub type St2cmp0R = crate::BitReader;
#[doc = "Field `ST2CMP0` writer - Slave_TIMER2 compare 0 event triggers bunch mode operation"]
pub type St2cmp0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2CMP1` reader - Slave_TIMER2 compare 1 event triggers bunch mode operation"]
pub type St2cmp1R = crate::BitReader;
#[doc = "Field `ST2CMP1` writer - Slave_TIMER2 compare 1 event triggers bunch mode operation"]
pub type St2cmp1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3RST` reader - Slave_TIMER3 reset event triggers bunch mode operation"]
pub type St3rstR = crate::BitReader;
#[doc = "Field `ST3RST` writer - Slave_TIMER3 reset event triggers bunch mode operation"]
pub type St3rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3REP` reader - Slave_TIMER3 repetition event triggers bunch mode operation"]
pub type St3repR = crate::BitReader;
#[doc = "Field `ST3REP` writer - Slave_TIMER3 repetition event triggers bunch mode operation"]
pub type St3repW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3CMP0` reader - Slave_TIMER3 compare 0 event triggers bunch mode operation"]
pub type St3cmp0R = crate::BitReader;
#[doc = "Field `ST3CMP0` writer - Slave_TIMER3 compare 0 event triggers bunch mode operation"]
pub type St3cmp0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3CMP1` reader - Slave_TIMER3 compare 1 event triggers bunch mode operation"]
pub type St3cmp1R = crate::BitReader;
#[doc = "Field `ST3CMP1` writer - Slave_TIMER3 compare 1 event triggers bunch mode operation"]
pub type St3cmp1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4RST` reader - Slave_TIMER4 reset event triggers bunch mode operation"]
pub type St4rstR = crate::BitReader;
#[doc = "Field `ST4RST` writer - Slave_TIMER4 reset event triggers bunch mode operation"]
pub type St4rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4REP` reader - Slave_TIMER4 repetition event triggers bunch mode operation"]
pub type St4repR = crate::BitReader;
#[doc = "Field `ST4REP` writer - Slave_TIMER4 repetition event triggers bunch mode operation"]
pub type St4repW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4CMP0` reader - Slave_TIMER4 compare 0 event triggers bunch mode operation"]
pub type St4cmp0R = crate::BitReader;
#[doc = "Field `ST4CMP0` writer - Slave_TIMER4 compare 0 event triggers bunch mode operation"]
pub type St4cmp0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4CMP1` reader - Slave_TIMER4 compare 1 event triggers bunch mode operation"]
pub type St4cmp1R = crate::BitReader;
#[doc = "Field `ST4CMP1` writer - Slave_TIMER4 compare 1 event triggers bunch mode operation"]
pub type St4cmp1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST0EXEV6` reader - Slave_TIMER0 period event following external event 6 triggers bunch mode operation"]
pub type St0exev6R = crate::BitReader;
#[doc = "Field `ST0EXEV6` writer - Slave_TIMER0 period event following external event 6 triggers bunch mode operation"]
pub type St0exev6W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3EXEV7` reader - Slave_TIMER3 period event following external event 7 triggers bunch mode operation"]
pub type St3exev7R = crate::BitReader;
#[doc = "Field `ST3EXEV7` writer - Slave_TIMER3 period event following external event 7 triggers bunch mode operation"]
pub type St3exev7W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV6` reader - External event 6 triggers bunch mode operation"]
pub type Exev6R = crate::BitReader;
#[doc = "Field `EXEV6` writer - External event 6 triggers bunch mode operation"]
pub type Exev6W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV7` reader - External event 7 triggers bunch mode operation"]
pub type Exev7R = crate::BitReader;
#[doc = "Field `EXEV7` writer - External event 7 triggers bunch mode operation"]
pub type Exev7W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CISGN` reader - Chip internal signal triggers bunch mode operation"]
pub type CisgnR = crate::BitReader;
#[doc = "Field `CISGN` writer - Chip internal signal triggers bunch mode operation"]
pub type CisgnW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Software triggers bunch mode operation"]
    #[inline(always)]
    pub fn swtrg(&self) -> SwtrgR {
        SwtrgR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Master_TIMER reset event triggers bunch mode operation"]
    #[inline(always)]
    pub fn mtrst(&self) -> MtrstR {
        MtrstR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Master_TIMER repetition event triggers bunch mode operation"]
    #[inline(always)]
    pub fn mtrep(&self) -> MtrepR {
        MtrepR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Master_TIMER compare 0 event triggers bunch mode operation"]
    #[inline(always)]
    pub fn mtcmp0(&self) -> Mtcmp0R {
        Mtcmp0R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Master_TIMER compare 1 event triggers bunch mode operation"]
    #[inline(always)]
    pub fn mtcmp1(&self) -> Mtcmp1R {
        Mtcmp1R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Master_TIMER compare 2 event triggers bunch mode operation"]
    #[inline(always)]
    pub fn mtcmp2(&self) -> Mtcmp2R {
        Mtcmp2R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Master_TIMER compare 3 event triggers bunch mode operation"]
    #[inline(always)]
    pub fn mtcmp3(&self) -> Mtcmp3R {
        Mtcmp3R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Slave_TIMER0 reset event triggers bunch mode operation"]
    #[inline(always)]
    pub fn st0rst(&self) -> St0rstR {
        St0rstR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Slave_TIMER0 repetition event triggers bunch mode operation"]
    #[inline(always)]
    pub fn st0rep(&self) -> St0repR {
        St0repR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Slave_TIMER0 compare 0 event triggers bunch mode operation"]
    #[inline(always)]
    pub fn st0cmp0(&self) -> St0cmp0R {
        St0cmp0R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Slave_TIMER0 compare 1 event triggers bunch mode operation"]
    #[inline(always)]
    pub fn st0cmp1(&self) -> St0cmp1R {
        St0cmp1R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Slave_TIMER1 reset event triggers bunch mode operation"]
    #[inline(always)]
    pub fn st1rst(&self) -> St1rstR {
        St1rstR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Slave_TIMER1 repetition event triggers bunch mode operation"]
    #[inline(always)]
    pub fn st1rep(&self) -> St1repR {
        St1repR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Slave_TIMER1 compare 0 event triggers bunch mode operation"]
    #[inline(always)]
    pub fn st1cmp0(&self) -> St1cmp0R {
        St1cmp0R::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Slave_TIMER1 compare 1 event triggers bunch mode operation"]
    #[inline(always)]
    pub fn st1cmp1(&self) -> St1cmp1R {
        St1cmp1R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Slave_TIMER2 reset event triggers bunch mode operation"]
    #[inline(always)]
    pub fn st2rst(&self) -> St2rstR {
        St2rstR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - Slave_TIMER1 repetition event triggers bunch mode operation"]
    #[inline(always)]
    pub fn st2rep(&self) -> St2repR {
        St2repR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - Slave_TIMER2 compare 0 event triggers bunch mode operation"]
    #[inline(always)]
    pub fn st2cmp0(&self) -> St2cmp0R {
        St2cmp0R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - Slave_TIMER2 compare 1 event triggers bunch mode operation"]
    #[inline(always)]
    pub fn st2cmp1(&self) -> St2cmp1R {
        St2cmp1R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - Slave_TIMER3 reset event triggers bunch mode operation"]
    #[inline(always)]
    pub fn st3rst(&self) -> St3rstR {
        St3rstR::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - Slave_TIMER3 repetition event triggers bunch mode operation"]
    #[inline(always)]
    pub fn st3rep(&self) -> St3repR {
        St3repR::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - Slave_TIMER3 compare 0 event triggers bunch mode operation"]
    #[inline(always)]
    pub fn st3cmp0(&self) -> St3cmp0R {
        St3cmp0R::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 22 - Slave_TIMER3 compare 1 event triggers bunch mode operation"]
    #[inline(always)]
    pub fn st3cmp1(&self) -> St3cmp1R {
        St3cmp1R::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 23 - Slave_TIMER4 reset event triggers bunch mode operation"]
    #[inline(always)]
    pub fn st4rst(&self) -> St4rstR {
        St4rstR::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bit 24 - Slave_TIMER4 repetition event triggers bunch mode operation"]
    #[inline(always)]
    pub fn st4rep(&self) -> St4repR {
        St4repR::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - Slave_TIMER4 compare 0 event triggers bunch mode operation"]
    #[inline(always)]
    pub fn st4cmp0(&self) -> St4cmp0R {
        St4cmp0R::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - Slave_TIMER4 compare 1 event triggers bunch mode operation"]
    #[inline(always)]
    pub fn st4cmp1(&self) -> St4cmp1R {
        St4cmp1R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - Slave_TIMER0 period event following external event 6 triggers bunch mode operation"]
    #[inline(always)]
    pub fn st0exev6(&self) -> St0exev6R {
        St0exev6R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - Slave_TIMER3 period event following external event 7 triggers bunch mode operation"]
    #[inline(always)]
    pub fn st3exev7(&self) -> St3exev7R {
        St3exev7R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - External event 6 triggers bunch mode operation"]
    #[inline(always)]
    pub fn exev6(&self) -> Exev6R {
        Exev6R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - External event 7 triggers bunch mode operation"]
    #[inline(always)]
    pub fn exev7(&self) -> Exev7R {
        Exev7R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - Chip internal signal triggers bunch mode operation"]
    #[inline(always)]
    pub fn cisgn(&self) -> CisgnR {
        CisgnR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Software triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn swtrg(&mut self) -> SwtrgW<BmstrgSpec> {
        SwtrgW::new(self, 0)
    }
    #[doc = "Bit 1 - Master_TIMER reset event triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn mtrst(&mut self) -> MtrstW<BmstrgSpec> {
        MtrstW::new(self, 1)
    }
    #[doc = "Bit 2 - Master_TIMER repetition event triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn mtrep(&mut self) -> MtrepW<BmstrgSpec> {
        MtrepW::new(self, 2)
    }
    #[doc = "Bit 3 - Master_TIMER compare 0 event triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn mtcmp0(&mut self) -> Mtcmp0W<BmstrgSpec> {
        Mtcmp0W::new(self, 3)
    }
    #[doc = "Bit 4 - Master_TIMER compare 1 event triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn mtcmp1(&mut self) -> Mtcmp1W<BmstrgSpec> {
        Mtcmp1W::new(self, 4)
    }
    #[doc = "Bit 5 - Master_TIMER compare 2 event triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn mtcmp2(&mut self) -> Mtcmp2W<BmstrgSpec> {
        Mtcmp2W::new(self, 5)
    }
    #[doc = "Bit 6 - Master_TIMER compare 3 event triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn mtcmp3(&mut self) -> Mtcmp3W<BmstrgSpec> {
        Mtcmp3W::new(self, 6)
    }
    #[doc = "Bit 7 - Slave_TIMER0 reset event triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn st0rst(&mut self) -> St0rstW<BmstrgSpec> {
        St0rstW::new(self, 7)
    }
    #[doc = "Bit 8 - Slave_TIMER0 repetition event triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn st0rep(&mut self) -> St0repW<BmstrgSpec> {
        St0repW::new(self, 8)
    }
    #[doc = "Bit 9 - Slave_TIMER0 compare 0 event triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn st0cmp0(&mut self) -> St0cmp0W<BmstrgSpec> {
        St0cmp0W::new(self, 9)
    }
    #[doc = "Bit 10 - Slave_TIMER0 compare 1 event triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn st0cmp1(&mut self) -> St0cmp1W<BmstrgSpec> {
        St0cmp1W::new(self, 10)
    }
    #[doc = "Bit 11 - Slave_TIMER1 reset event triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn st1rst(&mut self) -> St1rstW<BmstrgSpec> {
        St1rstW::new(self, 11)
    }
    #[doc = "Bit 12 - Slave_TIMER1 repetition event triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn st1rep(&mut self) -> St1repW<BmstrgSpec> {
        St1repW::new(self, 12)
    }
    #[doc = "Bit 13 - Slave_TIMER1 compare 0 event triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn st1cmp0(&mut self) -> St1cmp0W<BmstrgSpec> {
        St1cmp0W::new(self, 13)
    }
    #[doc = "Bit 14 - Slave_TIMER1 compare 1 event triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn st1cmp1(&mut self) -> St1cmp1W<BmstrgSpec> {
        St1cmp1W::new(self, 14)
    }
    #[doc = "Bit 15 - Slave_TIMER2 reset event triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn st2rst(&mut self) -> St2rstW<BmstrgSpec> {
        St2rstW::new(self, 15)
    }
    #[doc = "Bit 16 - Slave_TIMER1 repetition event triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn st2rep(&mut self) -> St2repW<BmstrgSpec> {
        St2repW::new(self, 16)
    }
    #[doc = "Bit 17 - Slave_TIMER2 compare 0 event triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn st2cmp0(&mut self) -> St2cmp0W<BmstrgSpec> {
        St2cmp0W::new(self, 17)
    }
    #[doc = "Bit 18 - Slave_TIMER2 compare 1 event triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn st2cmp1(&mut self) -> St2cmp1W<BmstrgSpec> {
        St2cmp1W::new(self, 18)
    }
    #[doc = "Bit 19 - Slave_TIMER3 reset event triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn st3rst(&mut self) -> St3rstW<BmstrgSpec> {
        St3rstW::new(self, 19)
    }
    #[doc = "Bit 20 - Slave_TIMER3 repetition event triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn st3rep(&mut self) -> St3repW<BmstrgSpec> {
        St3repW::new(self, 20)
    }
    #[doc = "Bit 21 - Slave_TIMER3 compare 0 event triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn st3cmp0(&mut self) -> St3cmp0W<BmstrgSpec> {
        St3cmp0W::new(self, 21)
    }
    #[doc = "Bit 22 - Slave_TIMER3 compare 1 event triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn st3cmp1(&mut self) -> St3cmp1W<BmstrgSpec> {
        St3cmp1W::new(self, 22)
    }
    #[doc = "Bit 23 - Slave_TIMER4 reset event triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn st4rst(&mut self) -> St4rstW<BmstrgSpec> {
        St4rstW::new(self, 23)
    }
    #[doc = "Bit 24 - Slave_TIMER4 repetition event triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn st4rep(&mut self) -> St4repW<BmstrgSpec> {
        St4repW::new(self, 24)
    }
    #[doc = "Bit 25 - Slave_TIMER4 compare 0 event triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn st4cmp0(&mut self) -> St4cmp0W<BmstrgSpec> {
        St4cmp0W::new(self, 25)
    }
    #[doc = "Bit 26 - Slave_TIMER4 compare 1 event triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn st4cmp1(&mut self) -> St4cmp1W<BmstrgSpec> {
        St4cmp1W::new(self, 26)
    }
    #[doc = "Bit 27 - Slave_TIMER0 period event following external event 6 triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn st0exev6(&mut self) -> St0exev6W<BmstrgSpec> {
        St0exev6W::new(self, 27)
    }
    #[doc = "Bit 28 - Slave_TIMER3 period event following external event 7 triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn st3exev7(&mut self) -> St3exev7W<BmstrgSpec> {
        St3exev7W::new(self, 28)
    }
    #[doc = "Bit 29 - External event 6 triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn exev6(&mut self) -> Exev6W<BmstrgSpec> {
        Exev6W::new(self, 29)
    }
    #[doc = "Bit 30 - External event 7 triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn exev7(&mut self) -> Exev7W<BmstrgSpec> {
        Exev7W::new(self, 30)
    }
    #[doc = "Bit 31 - Chip internal signal triggers bunch mode operation"]
    #[inline(always)]
    #[must_use]
    pub fn cisgn(&mut self) -> CisgnW<BmstrgSpec> {
        CisgnW::new(self, 31)
    }
}
#[doc = "SHRTIMER bunch mode start trigger register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`bmstrg::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`bmstrg::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct BmstrgSpec;
impl crate::RegisterSpec for BmstrgSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`bmstrg::R`](R) reader structure"]
impl crate::Readable for BmstrgSpec {}
#[doc = "`write(|w| ..)` method takes [`bmstrg::W`](W) writer structure"]
impl crate::Writable for BmstrgSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets BMSTRG to value 0"]
impl crate::Resettable for BmstrgSpec {
    const RESET_VALUE: u32 = 0;
}
