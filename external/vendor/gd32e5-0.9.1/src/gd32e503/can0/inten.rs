#[doc = "Register `INTEN` reader"]
pub type R = crate::R<IntenSpec>;
#[doc = "Register `INTEN` writer"]
pub type W = crate::W<IntenSpec>;
#[doc = "Field `TMEIE` reader - Transmit mailbox empty interrupt enable"]
pub type TmeieR = crate::BitReader;
#[doc = "Field `TMEIE` writer - Transmit mailbox empty interrupt enable"]
pub type TmeieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RFNEIE0` reader - Receive FIFO0 not empty interrupt enable"]
pub type Rfneie0R = crate::BitReader;
#[doc = "Field `RFNEIE0` writer - Receive FIFO0 not empty interrupt enable"]
pub type Rfneie0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RFFIE0` reader - Receive FIFO0 full interrupt enable"]
pub type Rffie0R = crate::BitReader;
#[doc = "Field `RFFIE0` writer - Receive FIFO0 full interrupt enable"]
pub type Rffie0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RFOIE0` reader - Receive FIFO0 overfull interrupt enable"]
pub type Rfoie0R = crate::BitReader;
#[doc = "Field `RFOIE0` writer - Receive FIFO0 overfull interrupt enable"]
pub type Rfoie0W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RFNEIE1` reader - Receive FIFO1 not empty interrupt enable"]
pub type Rfneie1R = crate::BitReader;
#[doc = "Field `RFNEIE1` writer - Receive FIFO1 not empty interrupt enable"]
pub type Rfneie1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RFFIE1` reader - Receive FIFO1 full interrupt enable"]
pub type Rffie1R = crate::BitReader;
#[doc = "Field `RFFIE1` writer - Receive FIFO1 full interrupt enable"]
pub type Rffie1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RFOIE1` reader - Receive FIFO1 overfull interrupt enable"]
pub type Rfoie1R = crate::BitReader;
#[doc = "Field `RFOIE1` writer - Receive FIFO1 overfull interrupt enable"]
pub type Rfoie1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WERRIE` reader - Warning error interrupt enable"]
pub type WerrieR = crate::BitReader;
#[doc = "Field `WERRIE` writer - Warning error interrupt enable"]
pub type WerrieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PERRIE` reader - Passive error interrupt enable"]
pub type PerrieR = crate::BitReader;
#[doc = "Field `PERRIE` writer - Passive error interrupt enable"]
pub type PerrieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BOIE` reader - Bus-off interrupt enable"]
pub type BoieR = crate::BitReader;
#[doc = "Field `BOIE` writer - Bus-off interrupt enable"]
pub type BoieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ERRNIE` reader - Error number interrupt enable"]
pub type ErrnieR = crate::BitReader;
#[doc = "Field `ERRNIE` writer - Error number interrupt enable"]
pub type ErrnieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ERRIE` reader - Error interrupt enable"]
pub type ErrieR = crate::BitReader;
#[doc = "Field `ERRIE` writer - Error interrupt enable"]
pub type ErrieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WIE` reader - Wakeup interrupt enable"]
pub type WieR = crate::BitReader;
#[doc = "Field `WIE` writer - Wakeup interrupt enable"]
pub type WieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SLPWIE` reader - Sleep working interrupt enable"]
pub type SlpwieR = crate::BitReader;
#[doc = "Field `SLPWIE` writer - Sleep working interrupt enable"]
pub type SlpwieW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Transmit mailbox empty interrupt enable"]
    #[inline(always)]
    pub fn tmeie(&self) -> TmeieR {
        TmeieR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Receive FIFO0 not empty interrupt enable"]
    #[inline(always)]
    pub fn rfneie0(&self) -> Rfneie0R {
        Rfneie0R::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Receive FIFO0 full interrupt enable"]
    #[inline(always)]
    pub fn rffie0(&self) -> Rffie0R {
        Rffie0R::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Receive FIFO0 overfull interrupt enable"]
    #[inline(always)]
    pub fn rfoie0(&self) -> Rfoie0R {
        Rfoie0R::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Receive FIFO1 not empty interrupt enable"]
    #[inline(always)]
    pub fn rfneie1(&self) -> Rfneie1R {
        Rfneie1R::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Receive FIFO1 full interrupt enable"]
    #[inline(always)]
    pub fn rffie1(&self) -> Rffie1R {
        Rffie1R::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Receive FIFO1 overfull interrupt enable"]
    #[inline(always)]
    pub fn rfoie1(&self) -> Rfoie1R {
        Rfoie1R::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 8 - Warning error interrupt enable"]
    #[inline(always)]
    pub fn werrie(&self) -> WerrieR {
        WerrieR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Passive error interrupt enable"]
    #[inline(always)]
    pub fn perrie(&self) -> PerrieR {
        PerrieR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Bus-off interrupt enable"]
    #[inline(always)]
    pub fn boie(&self) -> BoieR {
        BoieR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Error number interrupt enable"]
    #[inline(always)]
    pub fn errnie(&self) -> ErrnieR {
        ErrnieR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 15 - Error interrupt enable"]
    #[inline(always)]
    pub fn errie(&self) -> ErrieR {
        ErrieR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - Wakeup interrupt enable"]
    #[inline(always)]
    pub fn wie(&self) -> WieR {
        WieR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - Sleep working interrupt enable"]
    #[inline(always)]
    pub fn slpwie(&self) -> SlpwieR {
        SlpwieR::new(((self.bits >> 17) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Transmit mailbox empty interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn tmeie(&mut self) -> TmeieW<IntenSpec> {
        TmeieW::new(self, 0)
    }
    #[doc = "Bit 1 - Receive FIFO0 not empty interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn rfneie0(&mut self) -> Rfneie0W<IntenSpec> {
        Rfneie0W::new(self, 1)
    }
    #[doc = "Bit 2 - Receive FIFO0 full interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn rffie0(&mut self) -> Rffie0W<IntenSpec> {
        Rffie0W::new(self, 2)
    }
    #[doc = "Bit 3 - Receive FIFO0 overfull interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn rfoie0(&mut self) -> Rfoie0W<IntenSpec> {
        Rfoie0W::new(self, 3)
    }
    #[doc = "Bit 4 - Receive FIFO1 not empty interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn rfneie1(&mut self) -> Rfneie1W<IntenSpec> {
        Rfneie1W::new(self, 4)
    }
    #[doc = "Bit 5 - Receive FIFO1 full interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn rffie1(&mut self) -> Rffie1W<IntenSpec> {
        Rffie1W::new(self, 5)
    }
    #[doc = "Bit 6 - Receive FIFO1 overfull interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn rfoie1(&mut self) -> Rfoie1W<IntenSpec> {
        Rfoie1W::new(self, 6)
    }
    #[doc = "Bit 8 - Warning error interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn werrie(&mut self) -> WerrieW<IntenSpec> {
        WerrieW::new(self, 8)
    }
    #[doc = "Bit 9 - Passive error interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn perrie(&mut self) -> PerrieW<IntenSpec> {
        PerrieW::new(self, 9)
    }
    #[doc = "Bit 10 - Bus-off interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn boie(&mut self) -> BoieW<IntenSpec> {
        BoieW::new(self, 10)
    }
    #[doc = "Bit 11 - Error number interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn errnie(&mut self) -> ErrnieW<IntenSpec> {
        ErrnieW::new(self, 11)
    }
    #[doc = "Bit 15 - Error interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn errie(&mut self) -> ErrieW<IntenSpec> {
        ErrieW::new(self, 15)
    }
    #[doc = "Bit 16 - Wakeup interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn wie(&mut self) -> WieW<IntenSpec> {
        WieW::new(self, 16)
    }
    #[doc = "Bit 17 - Sleep working interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn slpwie(&mut self) -> SlpwieW<IntenSpec> {
        SlpwieW::new(self, 17)
    }
}
#[doc = "Interrupt enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`inten::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`inten::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IntenSpec;
impl crate::RegisterSpec for IntenSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`inten::R`](R) reader structure"]
impl crate::Readable for IntenSpec {}
#[doc = "`write(|w| ..)` method takes [`inten::W`](W) writer structure"]
impl crate::Writable for IntenSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets INTEN to value 0"]
impl crate::Resettable for IntenSpec {
    const RESET_VALUE: u32 = 0;
}
