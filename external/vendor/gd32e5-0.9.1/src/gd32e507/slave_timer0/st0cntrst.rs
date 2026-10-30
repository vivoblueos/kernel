#[doc = "Register `ST0CNTRST` reader"]
pub type R = crate::R<St0cntrstSpec>;
#[doc = "Register `ST0CNTRST` writer"]
pub type W = crate::W<St0cntrstSpec>;
#[doc = "Field `UPRST` reader - Slave_TIMER0 update event resets counter"]
pub type UprstR = crate::BitReader;
#[doc = "Field `UPRST` writer - Slave_TIMER0 update event resets counter"]
pub type UprstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMP1RST` reader - Slave_TIMER0 compare 1 event resets counter"]
pub type Cmp1rstR = crate::BitReader;
#[doc = "Field `CMP1RST` writer - Slave_TIMER0 compare 1 event resets counter"]
pub type Cmp1rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMP3RST` reader - Slave_TIMER0 compare 3 event resets counter"]
pub type Cmp3rstR = crate::BitReader;
#[doc = "Field `CMP3RST` writer - Slave_TIMER0 compare 3 event resets counter"]
pub type Cmp3rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTPERRST` reader - Master_TIMER period event resets counter"]
pub type MtperrstR = crate::BitReader;
#[doc = "Field `MTPERRST` writer - Master_TIMER period event resets counter"]
pub type MtperrstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTCMP0RST` reader - Master_TIMER compare 0 event resets counter"]
pub type Mtcmp0rstR = crate::BitReader;
#[doc = "Field `MTCMP0RST` writer - Master_TIMER compare 0 event resets counter"]
pub type Mtcmp0rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTCMP1RST` reader - Master_TIMER compare 1 event resets counter"]
pub type Mtcmp1rstR = crate::BitReader;
#[doc = "Field `MTCMP1RST` writer - Master_TIMER compare 1 event resets counter"]
pub type Mtcmp1rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTCMP2RST` reader - Master_TIMER compare 2 event resets counter"]
pub type Mtcmp2rstR = crate::BitReader;
#[doc = "Field `MTCMP2RST` writer - Master_TIMER compare 2 event resets counter"]
pub type Mtcmp2rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTCMP3RST` reader - Master_TIMER compare 3 event resets counter"]
pub type Mtcmp3rstR = crate::BitReader;
#[doc = "Field `MTCMP3RST` writer - Master_TIMER compare 3 event resets counter"]
pub type Mtcmp3rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV0RST` reader - External event 0 resets counter"]
pub type Exev0rstR = crate::BitReader;
#[doc = "Field `EXEV0RST` writer - External event 0 resets counter"]
pub type Exev0rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV1RST` reader - External event 1 resets counter"]
pub type Exev1rstR = crate::BitReader;
#[doc = "Field `EXEV1RST` writer - External event 1 resets counter"]
pub type Exev1rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV2RST` reader - External event 2 resets counter"]
pub type Exev2rstR = crate::BitReader;
#[doc = "Field `EXEV2RST` writer - External event 2 resets counter"]
pub type Exev2rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV3RST` reader - External event 3 resets counter"]
pub type Exev3rstR = crate::BitReader;
#[doc = "Field `EXEV3RST` writer - External event 3 resets counter"]
pub type Exev3rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV4RST` reader - External event 4 resets counter"]
pub type Exev4rstR = crate::BitReader;
#[doc = "Field `EXEV4RST` writer - External event 4 resets counter"]
pub type Exev4rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV5RST` reader - External event 5 resets counter"]
pub type Exev5rstR = crate::BitReader;
#[doc = "Field `EXEV5RST` writer - External event 5 resets counter"]
pub type Exev5rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV6RST` reader - External event 6 resets counter"]
pub type Exev6rstR = crate::BitReader;
#[doc = "Field `EXEV6RST` writer - External event 6 resets counter"]
pub type Exev6rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV7RST` reader - External event 7 resets counter"]
pub type Exev7rstR = crate::BitReader;
#[doc = "Field `EXEV7RST` writer - External event 7 resets counter"]
pub type Exev7rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV8RST` reader - External event 8 resets counter"]
pub type Exev8rstR = crate::BitReader;
#[doc = "Field `EXEV8RST` writer - External event 8 resets counter"]
pub type Exev8rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXEV9RST` reader - External event 9 resets counter"]
pub type Exev9rstR = crate::BitReader;
#[doc = "Field `EXEV9RST` writer - External event 9 resets counter"]
pub type Exev9rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1CMP0RST` reader - Slave_TIMER1 compare 0 event resets counter"]
pub type St1cmp0rstR = crate::BitReader;
#[doc = "Field `ST1CMP0RST` writer - Slave_TIMER1 compare 0 event resets counter"]
pub type St1cmp0rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1CMP1RST` reader - Slave_TIMER1 compare 1 event resets counter"]
pub type St1cmp1rstR = crate::BitReader;
#[doc = "Field `ST1CMP1RST` writer - Slave_TIMER1 compare 1 event resets counter"]
pub type St1cmp1rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST1CMP3RST` reader - Slave_TIMER1 compare 3 event resets counter"]
pub type St1cmp3rstR = crate::BitReader;
#[doc = "Field `ST1CMP3RST` writer - Slave_TIMER1 compare 3 event resets counter"]
pub type St1cmp3rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2CMP0RST` reader - Slave_TIMER2 compare 0 event resets counter"]
pub type St2cmp0rstR = crate::BitReader;
#[doc = "Field `ST2CMP0RST` writer - Slave_TIMER2 compare 0 event resets counter"]
pub type St2cmp0rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2CMP1RST` reader - Slave_TIMER2 compare 1 event resets counter"]
pub type St2cmp1rstR = crate::BitReader;
#[doc = "Field `ST2CMP1RST` writer - Slave_TIMER2 compare 1 event resets counter"]
pub type St2cmp1rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST2CMP3RST` reader - Slave_TIMER2 compare 3 event resets counter"]
pub type St2cmp3rstR = crate::BitReader;
#[doc = "Field `ST2CMP3RST` writer - Slave_TIMER2 compare 3 event resets counter"]
pub type St2cmp3rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3CMP0RST` reader - Slave_TIMER3 compare 0 event resets counter"]
pub type St3cmp0rstR = crate::BitReader;
#[doc = "Field `ST3CMP0RST` writer - Slave_TIMER3 compare 0 event resets counter"]
pub type St3cmp0rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3CMP1RST` reader - Slave_TIMER3 compare 1 event resets counter"]
pub type St3cmp1rstR = crate::BitReader;
#[doc = "Field `ST3CMP1RST` writer - Slave_TIMER3 compare 1 event resets counter"]
pub type St3cmp1rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST3CMP3RST` reader - Slave_TIMER3 compare 3 event resets counter"]
pub type St3cmp3rstR = crate::BitReader;
#[doc = "Field `ST3CMP3RST` writer - Slave_TIMER3 compare 3 event resets counter"]
pub type St3cmp3rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4CMP0RST` reader - Slave_TIMER4 compare 0 event resets counter"]
pub type St4cmp0rstR = crate::BitReader;
#[doc = "Field `ST4CMP0RST` writer - Slave_TIMER4 compare 0 event resets counter"]
pub type St4cmp0rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4CMP1RST` reader - Slave_TIMER4 compare 1 event resets counter"]
pub type St4cmp1rstR = crate::BitReader;
#[doc = "Field `ST4CMP1RST` writer - Slave_TIMER4 compare 1 event resets counter"]
pub type St4cmp1rstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ST4CMP3RST` reader - Slave_TIMER4 compare 3 event resets counter"]
pub type St4cmp3rstR = crate::BitReader;
#[doc = "Field `ST4CMP3RST` writer - Slave_TIMER4 compare 3 event resets counter"]
pub type St4cmp3rstW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 1 - Slave_TIMER0 update event resets counter"]
    #[inline(always)]
    pub fn uprst(&self) -> UprstR {
        UprstR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Slave_TIMER0 compare 1 event resets counter"]
    #[inline(always)]
    pub fn cmp1rst(&self) -> Cmp1rstR {
        Cmp1rstR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Slave_TIMER0 compare 3 event resets counter"]
    #[inline(always)]
    pub fn cmp3rst(&self) -> Cmp3rstR {
        Cmp3rstR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Master_TIMER period event resets counter"]
    #[inline(always)]
    pub fn mtperrst(&self) -> MtperrstR {
        MtperrstR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Master_TIMER compare 0 event resets counter"]
    #[inline(always)]
    pub fn mtcmp0rst(&self) -> Mtcmp0rstR {
        Mtcmp0rstR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Master_TIMER compare 1 event resets counter"]
    #[inline(always)]
    pub fn mtcmp1rst(&self) -> Mtcmp1rstR {
        Mtcmp1rstR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Master_TIMER compare 2 event resets counter"]
    #[inline(always)]
    pub fn mtcmp2rst(&self) -> Mtcmp2rstR {
        Mtcmp2rstR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Master_TIMER compare 3 event resets counter"]
    #[inline(always)]
    pub fn mtcmp3rst(&self) -> Mtcmp3rstR {
        Mtcmp3rstR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - External event 0 resets counter"]
    #[inline(always)]
    pub fn exev0rst(&self) -> Exev0rstR {
        Exev0rstR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - External event 1 resets counter"]
    #[inline(always)]
    pub fn exev1rst(&self) -> Exev1rstR {
        Exev1rstR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - External event 2 resets counter"]
    #[inline(always)]
    pub fn exev2rst(&self) -> Exev2rstR {
        Exev2rstR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - External event 3 resets counter"]
    #[inline(always)]
    pub fn exev3rst(&self) -> Exev3rstR {
        Exev3rstR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - External event 4 resets counter"]
    #[inline(always)]
    pub fn exev4rst(&self) -> Exev4rstR {
        Exev4rstR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - External event 5 resets counter"]
    #[inline(always)]
    pub fn exev5rst(&self) -> Exev5rstR {
        Exev5rstR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - External event 6 resets counter"]
    #[inline(always)]
    pub fn exev6rst(&self) -> Exev6rstR {
        Exev6rstR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - External event 7 resets counter"]
    #[inline(always)]
    pub fn exev7rst(&self) -> Exev7rstR {
        Exev7rstR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - External event 8 resets counter"]
    #[inline(always)]
    pub fn exev8rst(&self) -> Exev8rstR {
        Exev8rstR::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - External event 9 resets counter"]
    #[inline(always)]
    pub fn exev9rst(&self) -> Exev9rstR {
        Exev9rstR::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - Slave_TIMER1 compare 0 event resets counter"]
    #[inline(always)]
    pub fn st1cmp0rst(&self) -> St1cmp0rstR {
        St1cmp0rstR::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - Slave_TIMER1 compare 1 event resets counter"]
    #[inline(always)]
    pub fn st1cmp1rst(&self) -> St1cmp1rstR {
        St1cmp1rstR::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - Slave_TIMER1 compare 3 event resets counter"]
    #[inline(always)]
    pub fn st1cmp3rst(&self) -> St1cmp3rstR {
        St1cmp3rstR::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 22 - Slave_TIMER2 compare 0 event resets counter"]
    #[inline(always)]
    pub fn st2cmp0rst(&self) -> St2cmp0rstR {
        St2cmp0rstR::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 23 - Slave_TIMER2 compare 1 event resets counter"]
    #[inline(always)]
    pub fn st2cmp1rst(&self) -> St2cmp1rstR {
        St2cmp1rstR::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bit 24 - Slave_TIMER2 compare 3 event resets counter"]
    #[inline(always)]
    pub fn st2cmp3rst(&self) -> St2cmp3rstR {
        St2cmp3rstR::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - Slave_TIMER3 compare 0 event resets counter"]
    #[inline(always)]
    pub fn st3cmp0rst(&self) -> St3cmp0rstR {
        St3cmp0rstR::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - Slave_TIMER3 compare 1 event resets counter"]
    #[inline(always)]
    pub fn st3cmp1rst(&self) -> St3cmp1rstR {
        St3cmp1rstR::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - Slave_TIMER3 compare 3 event resets counter"]
    #[inline(always)]
    pub fn st3cmp3rst(&self) -> St3cmp3rstR {
        St3cmp3rstR::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - Slave_TIMER4 compare 0 event resets counter"]
    #[inline(always)]
    pub fn st4cmp0rst(&self) -> St4cmp0rstR {
        St4cmp0rstR::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - Slave_TIMER4 compare 1 event resets counter"]
    #[inline(always)]
    pub fn st4cmp1rst(&self) -> St4cmp1rstR {
        St4cmp1rstR::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - Slave_TIMER4 compare 3 event resets counter"]
    #[inline(always)]
    pub fn st4cmp3rst(&self) -> St4cmp3rstR {
        St4cmp3rstR::new(((self.bits >> 30) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 1 - Slave_TIMER0 update event resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn uprst(&mut self) -> UprstW<St0cntrstSpec> {
        UprstW::new(self, 1)
    }
    #[doc = "Bit 2 - Slave_TIMER0 compare 1 event resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn cmp1rst(&mut self) -> Cmp1rstW<St0cntrstSpec> {
        Cmp1rstW::new(self, 2)
    }
    #[doc = "Bit 3 - Slave_TIMER0 compare 3 event resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn cmp3rst(&mut self) -> Cmp3rstW<St0cntrstSpec> {
        Cmp3rstW::new(self, 3)
    }
    #[doc = "Bit 4 - Master_TIMER period event resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn mtperrst(&mut self) -> MtperrstW<St0cntrstSpec> {
        MtperrstW::new(self, 4)
    }
    #[doc = "Bit 5 - Master_TIMER compare 0 event resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn mtcmp0rst(&mut self) -> Mtcmp0rstW<St0cntrstSpec> {
        Mtcmp0rstW::new(self, 5)
    }
    #[doc = "Bit 6 - Master_TIMER compare 1 event resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn mtcmp1rst(&mut self) -> Mtcmp1rstW<St0cntrstSpec> {
        Mtcmp1rstW::new(self, 6)
    }
    #[doc = "Bit 7 - Master_TIMER compare 2 event resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn mtcmp2rst(&mut self) -> Mtcmp2rstW<St0cntrstSpec> {
        Mtcmp2rstW::new(self, 7)
    }
    #[doc = "Bit 8 - Master_TIMER compare 3 event resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn mtcmp3rst(&mut self) -> Mtcmp3rstW<St0cntrstSpec> {
        Mtcmp3rstW::new(self, 8)
    }
    #[doc = "Bit 9 - External event 0 resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn exev0rst(&mut self) -> Exev0rstW<St0cntrstSpec> {
        Exev0rstW::new(self, 9)
    }
    #[doc = "Bit 10 - External event 1 resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn exev1rst(&mut self) -> Exev1rstW<St0cntrstSpec> {
        Exev1rstW::new(self, 10)
    }
    #[doc = "Bit 11 - External event 2 resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn exev2rst(&mut self) -> Exev2rstW<St0cntrstSpec> {
        Exev2rstW::new(self, 11)
    }
    #[doc = "Bit 12 - External event 3 resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn exev3rst(&mut self) -> Exev3rstW<St0cntrstSpec> {
        Exev3rstW::new(self, 12)
    }
    #[doc = "Bit 13 - External event 4 resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn exev4rst(&mut self) -> Exev4rstW<St0cntrstSpec> {
        Exev4rstW::new(self, 13)
    }
    #[doc = "Bit 14 - External event 5 resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn exev5rst(&mut self) -> Exev5rstW<St0cntrstSpec> {
        Exev5rstW::new(self, 14)
    }
    #[doc = "Bit 15 - External event 6 resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn exev6rst(&mut self) -> Exev6rstW<St0cntrstSpec> {
        Exev6rstW::new(self, 15)
    }
    #[doc = "Bit 16 - External event 7 resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn exev7rst(&mut self) -> Exev7rstW<St0cntrstSpec> {
        Exev7rstW::new(self, 16)
    }
    #[doc = "Bit 17 - External event 8 resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn exev8rst(&mut self) -> Exev8rstW<St0cntrstSpec> {
        Exev8rstW::new(self, 17)
    }
    #[doc = "Bit 18 - External event 9 resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn exev9rst(&mut self) -> Exev9rstW<St0cntrstSpec> {
        Exev9rstW::new(self, 18)
    }
    #[doc = "Bit 19 - Slave_TIMER1 compare 0 event resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn st1cmp0rst(&mut self) -> St1cmp0rstW<St0cntrstSpec> {
        St1cmp0rstW::new(self, 19)
    }
    #[doc = "Bit 20 - Slave_TIMER1 compare 1 event resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn st1cmp1rst(&mut self) -> St1cmp1rstW<St0cntrstSpec> {
        St1cmp1rstW::new(self, 20)
    }
    #[doc = "Bit 21 - Slave_TIMER1 compare 3 event resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn st1cmp3rst(&mut self) -> St1cmp3rstW<St0cntrstSpec> {
        St1cmp3rstW::new(self, 21)
    }
    #[doc = "Bit 22 - Slave_TIMER2 compare 0 event resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn st2cmp0rst(&mut self) -> St2cmp0rstW<St0cntrstSpec> {
        St2cmp0rstW::new(self, 22)
    }
    #[doc = "Bit 23 - Slave_TIMER2 compare 1 event resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn st2cmp1rst(&mut self) -> St2cmp1rstW<St0cntrstSpec> {
        St2cmp1rstW::new(self, 23)
    }
    #[doc = "Bit 24 - Slave_TIMER2 compare 3 event resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn st2cmp3rst(&mut self) -> St2cmp3rstW<St0cntrstSpec> {
        St2cmp3rstW::new(self, 24)
    }
    #[doc = "Bit 25 - Slave_TIMER3 compare 0 event resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn st3cmp0rst(&mut self) -> St3cmp0rstW<St0cntrstSpec> {
        St3cmp0rstW::new(self, 25)
    }
    #[doc = "Bit 26 - Slave_TIMER3 compare 1 event resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn st3cmp1rst(&mut self) -> St3cmp1rstW<St0cntrstSpec> {
        St3cmp1rstW::new(self, 26)
    }
    #[doc = "Bit 27 - Slave_TIMER3 compare 3 event resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn st3cmp3rst(&mut self) -> St3cmp3rstW<St0cntrstSpec> {
        St3cmp3rstW::new(self, 27)
    }
    #[doc = "Bit 28 - Slave_TIMER4 compare 0 event resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn st4cmp0rst(&mut self) -> St4cmp0rstW<St0cntrstSpec> {
        St4cmp0rstW::new(self, 28)
    }
    #[doc = "Bit 29 - Slave_TIMER4 compare 1 event resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn st4cmp1rst(&mut self) -> St4cmp1rstW<St0cntrstSpec> {
        St4cmp1rstW::new(self, 29)
    }
    #[doc = "Bit 30 - Slave_TIMER4 compare 3 event resets counter"]
    #[inline(always)]
    #[must_use]
    pub fn st4cmp3rst(&mut self) -> St4cmp3rstW<St0cntrstSpec> {
        St4cmp3rstW::new(self, 30)
    }
}
#[doc = "SHRTIMER Slave_TIMER0 counter reset register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`st0cntrst::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`st0cntrst::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct St0cntrstSpec;
impl crate::RegisterSpec for St0cntrstSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`st0cntrst::R`](R) reader structure"]
impl crate::Readable for St0cntrstSpec {}
#[doc = "`write(|w| ..)` method takes [`st0cntrst::W`](W) writer structure"]
impl crate::Writable for St0cntrstSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets ST0CNTRST to value 0"]
impl crate::Resettable for St0cntrstSpec {
    const RESET_VALUE: u32 = 0;
}
