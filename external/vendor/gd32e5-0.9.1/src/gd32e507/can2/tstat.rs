#[doc = "Register `TSTAT` reader"]
pub type R = crate::R<TstatSpec>;
#[doc = "Register `TSTAT` writer"]
pub type W = crate::W<TstatSpec>;
#[doc = "Field `MTF0` reader - Mailbox 0 transmit finished"]
pub type Mtf0R = crate::BitReader;
#[doc = "Field `MTF0` writer - Mailbox 0 transmit finished"]
pub type Mtf0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTFNERR0` reader - Mailbox 0 transmit finished and no error"]
pub type Mtfnerr0R = crate::BitReader;
#[doc = "Field `MTFNERR0` writer - Mailbox 0 transmit finished and no error"]
pub type Mtfnerr0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MAL0` reader - Mailbox 0 arbitration lost"]
pub type Mal0R = crate::BitReader;
#[doc = "Field `MAL0` writer - Mailbox 0 arbitration lost"]
pub type Mal0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTE0` reader - Mailbox 0 transmit error"]
pub type Mte0R = crate::BitReader;
#[doc = "Field `MTE0` writer - Mailbox 0 transmit error"]
pub type Mte0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MST0` reader - Mailbox 0 stop transmitting"]
pub type Mst0R = crate::BitReader;
#[doc = "Field `MST0` writer - Mailbox 0 stop transmitting"]
pub type Mst0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTF1` reader - Mailbox 1 transmit finished"]
pub type Mtf1R = crate::BitReader;
#[doc = "Field `MTF1` writer - Mailbox 1 transmit finished"]
pub type Mtf1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTFNERR1` reader - Mailbox 1 transmit finished and no error"]
pub type Mtfnerr1R = crate::BitReader;
#[doc = "Field `MTFNERR1` writer - Mailbox 1 transmit finished and no error"]
pub type Mtfnerr1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MAL1` reader - Mailbox 1 arbitration lost"]
pub type Mal1R = crate::BitReader;
#[doc = "Field `MAL1` writer - Mailbox 1 arbitration lost"]
pub type Mal1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTE1` reader - Mailbox 1 transmit error"]
pub type Mte1R = crate::BitReader;
#[doc = "Field `MTE1` writer - Mailbox 1 transmit error"]
pub type Mte1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MST1` reader - Mailbox 1 stop transmitting"]
pub type Mst1R = crate::BitReader;
#[doc = "Field `MST1` writer - Mailbox 1 stop transmitting"]
pub type Mst1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTF2` reader - Mailbox 2 transmit finished"]
pub type Mtf2R = crate::BitReader;
#[doc = "Field `MTF2` writer - Mailbox 2 transmit finished"]
pub type Mtf2W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTFNERR2` reader - Mailbox 2 transmit finished and no error"]
pub type Mtfnerr2R = crate::BitReader;
#[doc = "Field `MTFNERR2` writer - Mailbox 2 transmit finished and no error"]
pub type Mtfnerr2W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MAL2` reader - Mailbox 2 arbitration lost"]
pub type Mal2R = crate::BitReader;
#[doc = "Field `MAL2` writer - Mailbox 2 arbitration lost"]
pub type Mal2W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MTE2` reader - Mailbox 2 transmit error"]
pub type Mte2R = crate::BitReader;
#[doc = "Field `MTE2` writer - Mailbox 2 transmit error"]
pub type Mte2W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MST2` reader - Mailbox 2 stop transmitting"]
pub type Mst2R = crate::BitReader;
#[doc = "Field `MST2` writer - Mailbox 2 stop transmitting"]
pub type Mst2W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `NUM` reader - number of the transmit FIFO mailbox in which the frame will be transmitted if at least one mailbox is empty"]
pub type NumR = crate::FieldReader;
#[doc = "Field `TME0` reader - Transmit mailbox 0 empty"]
pub type Tme0R = crate::BitReader;
#[doc = "Field `TME1` reader - Transmit mailbox 1 empty"]
pub type Tme1R = crate::BitReader;
#[doc = "Field `TME2` reader - Transmit mailbox 2 empty"]
pub type Tme2R = crate::BitReader;
#[doc = "Field `TMLS0` reader - Transmit mailbox 0 last sending in transmit FIFO"]
pub type Tmls0R = crate::BitReader;
#[doc = "Field `TMLS1` reader - Transmit mailbox 1 last sending in transmit FIFO"]
pub type Tmls1R = crate::BitReader;
#[doc = "Field `TMLS2` reader - Transmit mailbox 2 last sending in transmit FIFO"]
pub type Tmls2R = crate::BitReader;
impl R {
    #[doc = "Bit 0 - Mailbox 0 transmit finished"]
    #[inline(always)]
    pub fn mtf0(&self) -> Mtf0R {
        Mtf0R::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Mailbox 0 transmit finished and no error"]
    #[inline(always)]
    pub fn mtfnerr0(&self) -> Mtfnerr0R {
        Mtfnerr0R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Mailbox 0 arbitration lost"]
    #[inline(always)]
    pub fn mal0(&self) -> Mal0R {
        Mal0R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Mailbox 0 transmit error"]
    #[inline(always)]
    pub fn mte0(&self) -> Mte0R {
        Mte0R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 7 - Mailbox 0 stop transmitting"]
    #[inline(always)]
    pub fn mst0(&self) -> Mst0R {
        Mst0R::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Mailbox 1 transmit finished"]
    #[inline(always)]
    pub fn mtf1(&self) -> Mtf1R {
        Mtf1R::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Mailbox 1 transmit finished and no error"]
    #[inline(always)]
    pub fn mtfnerr1(&self) -> Mtfnerr1R {
        Mtfnerr1R::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Mailbox 1 arbitration lost"]
    #[inline(always)]
    pub fn mal1(&self) -> Mal1R {
        Mal1R::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Mailbox 1 transmit error"]
    #[inline(always)]
    pub fn mte1(&self) -> Mte1R {
        Mte1R::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 15 - Mailbox 1 stop transmitting"]
    #[inline(always)]
    pub fn mst1(&self) -> Mst1R {
        Mst1R::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - Mailbox 2 transmit finished"]
    #[inline(always)]
    pub fn mtf2(&self) -> Mtf2R {
        Mtf2R::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - Mailbox 2 transmit finished and no error"]
    #[inline(always)]
    pub fn mtfnerr2(&self) -> Mtfnerr2R {
        Mtfnerr2R::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - Mailbox 2 arbitration lost"]
    #[inline(always)]
    pub fn mal2(&self) -> Mal2R {
        Mal2R::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - Mailbox 2 transmit error"]
    #[inline(always)]
    pub fn mte2(&self) -> Mte2R {
        Mte2R::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 23 - Mailbox 2 stop transmitting"]
    #[inline(always)]
    pub fn mst2(&self) -> Mst2R {
        Mst2R::new(((self.bits >> 23) & 1) != 0)
    }
    #[doc = "Bits 24:25 - number of the transmit FIFO mailbox in which the frame will be transmitted if at least one mailbox is empty"]
    #[inline(always)]
    pub fn num(&self) -> NumR {
        NumR::new(((self.bits >> 24) & 3) as u8)
    }
    #[doc = "Bit 26 - Transmit mailbox 0 empty"]
    #[inline(always)]
    pub fn tme0(&self) -> Tme0R {
        Tme0R::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - Transmit mailbox 1 empty"]
    #[inline(always)]
    pub fn tme1(&self) -> Tme1R {
        Tme1R::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - Transmit mailbox 2 empty"]
    #[inline(always)]
    pub fn tme2(&self) -> Tme2R {
        Tme2R::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - Transmit mailbox 0 last sending in transmit FIFO"]
    #[inline(always)]
    pub fn tmls0(&self) -> Tmls0R {
        Tmls0R::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - Transmit mailbox 1 last sending in transmit FIFO"]
    #[inline(always)]
    pub fn tmls1(&self) -> Tmls1R {
        Tmls1R::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - Transmit mailbox 2 last sending in transmit FIFO"]
    #[inline(always)]
    pub fn tmls2(&self) -> Tmls2R {
        Tmls2R::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Mailbox 0 transmit finished"]
    #[inline(always)]
    #[must_use]
    pub fn mtf0(&mut self) -> Mtf0W<TstatSpec> {
        Mtf0W::new(self, 0)
    }
    #[doc = "Bit 1 - Mailbox 0 transmit finished and no error"]
    #[inline(always)]
    #[must_use]
    pub fn mtfnerr0(&mut self) -> Mtfnerr0W<TstatSpec> {
        Mtfnerr0W::new(self, 1)
    }
    #[doc = "Bit 2 - Mailbox 0 arbitration lost"]
    #[inline(always)]
    #[must_use]
    pub fn mal0(&mut self) -> Mal0W<TstatSpec> {
        Mal0W::new(self, 2)
    }
    #[doc = "Bit 3 - Mailbox 0 transmit error"]
    #[inline(always)]
    #[must_use]
    pub fn mte0(&mut self) -> Mte0W<TstatSpec> {
        Mte0W::new(self, 3)
    }
    #[doc = "Bit 7 - Mailbox 0 stop transmitting"]
    #[inline(always)]
    #[must_use]
    pub fn mst0(&mut self) -> Mst0W<TstatSpec> {
        Mst0W::new(self, 7)
    }
    #[doc = "Bit 8 - Mailbox 1 transmit finished"]
    #[inline(always)]
    #[must_use]
    pub fn mtf1(&mut self) -> Mtf1W<TstatSpec> {
        Mtf1W::new(self, 8)
    }
    #[doc = "Bit 9 - Mailbox 1 transmit finished and no error"]
    #[inline(always)]
    #[must_use]
    pub fn mtfnerr1(&mut self) -> Mtfnerr1W<TstatSpec> {
        Mtfnerr1W::new(self, 9)
    }
    #[doc = "Bit 10 - Mailbox 1 arbitration lost"]
    #[inline(always)]
    #[must_use]
    pub fn mal1(&mut self) -> Mal1W<TstatSpec> {
        Mal1W::new(self, 10)
    }
    #[doc = "Bit 11 - Mailbox 1 transmit error"]
    #[inline(always)]
    #[must_use]
    pub fn mte1(&mut self) -> Mte1W<TstatSpec> {
        Mte1W::new(self, 11)
    }
    #[doc = "Bit 15 - Mailbox 1 stop transmitting"]
    #[inline(always)]
    #[must_use]
    pub fn mst1(&mut self) -> Mst1W<TstatSpec> {
        Mst1W::new(self, 15)
    }
    #[doc = "Bit 16 - Mailbox 2 transmit finished"]
    #[inline(always)]
    #[must_use]
    pub fn mtf2(&mut self) -> Mtf2W<TstatSpec> {
        Mtf2W::new(self, 16)
    }
    #[doc = "Bit 17 - Mailbox 2 transmit finished and no error"]
    #[inline(always)]
    #[must_use]
    pub fn mtfnerr2(&mut self) -> Mtfnerr2W<TstatSpec> {
        Mtfnerr2W::new(self, 17)
    }
    #[doc = "Bit 18 - Mailbox 2 arbitration lost"]
    #[inline(always)]
    #[must_use]
    pub fn mal2(&mut self) -> Mal2W<TstatSpec> {
        Mal2W::new(self, 18)
    }
    #[doc = "Bit 19 - Mailbox 2 transmit error"]
    #[inline(always)]
    #[must_use]
    pub fn mte2(&mut self) -> Mte2W<TstatSpec> {
        Mte2W::new(self, 19)
    }
    #[doc = "Bit 23 - Mailbox 2 stop transmitting"]
    #[inline(always)]
    #[must_use]
    pub fn mst2(&mut self) -> Mst2W<TstatSpec> {
        Mst2W::new(self, 23)
    }
}
#[doc = "Transmit status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`tstat::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`tstat::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct TstatSpec;
impl crate::RegisterSpec for TstatSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`tstat::R`](R) reader structure"]
impl crate::Readable for TstatSpec {}
#[doc = "`write(|w| ..)` method takes [`tstat::W`](W) writer structure"]
impl crate::Writable for TstatSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets TSTAT to value 0x1c00_0000"]
impl crate::Resettable for TstatSpec {
    const RESET_VALUE: u32 = 0x1c00_0000;
}
