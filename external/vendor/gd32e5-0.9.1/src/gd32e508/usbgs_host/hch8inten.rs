#[doc = "Register `HCH8INTEN` reader"]
pub type R = crate::R<Hch8intenSpec>;
#[doc = "Register `HCH8INTEN` writer"]
pub type W = crate::W<Hch8intenSpec>;
#[doc = "Field `TFIE` reader - Transfer completed interrupt enable"]
pub type TfieR = crate::BitReader;
#[doc = "Field `TFIE` writer - Transfer completed interrupt enable"]
pub type TfieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CHIE` reader - Channel halted interrupt enable"]
pub type ChieR = crate::BitReader;
#[doc = "Field `CHIE` writer - Channel halted interrupt enable"]
pub type ChieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `STALLIE` reader - STALL interrupt enable"]
pub type StallieR = crate::BitReader;
#[doc = "Field `STALLIE` writer - STALL interrupt enable"]
pub type StallieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `NAKIE` reader - NAK interrupt enable"]
pub type NakieR = crate::BitReader;
#[doc = "Field `NAKIE` writer - NAK interrupt enable"]
pub type NakieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ACKIE` reader - ACK interrupt enable"]
pub type AckieR = crate::BitReader;
#[doc = "Field `ACKIE` writer - ACK interrupt enable"]
pub type AckieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `USBERIE` reader - USB bus error interrupt enable"]
pub type UsberieR = crate::BitReader;
#[doc = "Field `USBERIE` writer - USB bus error interrupt enable"]
pub type UsberieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BBERIE` reader - Babble error interrupt enable"]
pub type BberieR = crate::BitReader;
#[doc = "Field `BBERIE` writer - Babble error interrupt enable"]
pub type BberieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `REQOVRIE` reader - request queue overrun interrupt enable"]
pub type ReqovrieR = crate::BitReader;
#[doc = "Field `REQOVRIE` writer - request queue overrun interrupt enable"]
pub type ReqovrieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DTERIE` reader - Data toggle error interrupt enable"]
pub type DterieR = crate::BitReader;
#[doc = "Field `DTERIE` writer - Data toggle error interrupt enable"]
pub type DterieW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Transfer completed interrupt enable"]
    #[inline(always)]
    pub fn tfie(&self) -> TfieR {
        TfieR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Channel halted interrupt enable"]
    #[inline(always)]
    pub fn chie(&self) -> ChieR {
        ChieR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 3 - STALL interrupt enable"]
    #[inline(always)]
    pub fn stallie(&self) -> StallieR {
        StallieR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - NAK interrupt enable"]
    #[inline(always)]
    pub fn nakie(&self) -> NakieR {
        NakieR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - ACK interrupt enable"]
    #[inline(always)]
    pub fn ackie(&self) -> AckieR {
        AckieR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 7 - USB bus error interrupt enable"]
    #[inline(always)]
    pub fn usberie(&self) -> UsberieR {
        UsberieR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Babble error interrupt enable"]
    #[inline(always)]
    pub fn bberie(&self) -> BberieR {
        BberieR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - request queue overrun interrupt enable"]
    #[inline(always)]
    pub fn reqovrie(&self) -> ReqovrieR {
        ReqovrieR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Data toggle error interrupt enable"]
    #[inline(always)]
    pub fn dterie(&self) -> DterieR {
        DterieR::new(((self.bits >> 10) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Transfer completed interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn tfie(&mut self) -> TfieW<Hch8intenSpec> {
        TfieW::new(self, 0)
    }
    #[doc = "Bit 1 - Channel halted interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn chie(&mut self) -> ChieW<Hch8intenSpec> {
        ChieW::new(self, 1)
    }
    #[doc = "Bit 3 - STALL interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn stallie(&mut self) -> StallieW<Hch8intenSpec> {
        StallieW::new(self, 3)
    }
    #[doc = "Bit 4 - NAK interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn nakie(&mut self) -> NakieW<Hch8intenSpec> {
        NakieW::new(self, 4)
    }
    #[doc = "Bit 5 - ACK interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn ackie(&mut self) -> AckieW<Hch8intenSpec> {
        AckieW::new(self, 5)
    }
    #[doc = "Bit 7 - USB bus error interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn usberie(&mut self) -> UsberieW<Hch8intenSpec> {
        UsberieW::new(self, 7)
    }
    #[doc = "Bit 8 - Babble error interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn bberie(&mut self) -> BberieW<Hch8intenSpec> {
        BberieW::new(self, 8)
    }
    #[doc = "Bit 9 - request queue overrun interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn reqovrie(&mut self) -> ReqovrieW<Hch8intenSpec> {
        ReqovrieW::new(self, 9)
    }
    #[doc = "Bit 10 - Data toggle error interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn dterie(&mut self) -> DterieW<Hch8intenSpec> {
        DterieW::new(self, 10)
    }
}
#[doc = "host channel-8 interrupt enable register (HCH7INTEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`hch8inten::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`hch8inten::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Hch8intenSpec;
impl crate::RegisterSpec for Hch8intenSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`hch8inten::R`](R) reader structure"]
impl crate::Readable for Hch8intenSpec {}
#[doc = "`write(|w| ..)` method takes [`hch8inten::W`](W) writer structure"]
impl crate::Writable for Hch8intenSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets HCH8INTEN to value 0"]
impl crate::Resettable for Hch8intenSpec {
    const RESET_VALUE: u32 = 0;
}
