#[doc = "Register `DIEP1INTEN` reader"]
pub type R = crate::R<Diep1intenSpec>;
#[doc = "Register `DIEP1INTEN` writer"]
pub type W = crate::W<Diep1intenSpec>;
#[doc = "Field `TFEN` reader - Transfer finished interrupt enable bit"]
pub type TfenR = crate::BitReader;
#[doc = "Field `TFEN` writer - Transfer finished interrupt enable bit"]
pub type TfenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EPDISEN` reader - Endpoint disabled interrupt enable bit"]
pub type EpdisenR = crate::BitReader;
#[doc = "Field `EPDISEN` writer - Endpoint disabled interrupt enable bit"]
pub type EpdisenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CITOEN` reader - Control In Timeout interrupt enable bit"]
pub type CitoenR = crate::BitReader;
#[doc = "Field `CITOEN` writer - Control In Timeout interrupt enable bit"]
pub type CitoenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EPTXFUDEN` reader - Endpoint Tx FIFO underrun interrupt enable bit"]
pub type EptxfudenR = crate::BitReader;
#[doc = "Field `EPTXFUDEN` writer - Endpoint Tx FIFO underrun interrupt enable bit"]
pub type EptxfudenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IEPNEEN` reader - IN endpoint NAK effective interrupt enable bit"]
pub type IepneenR = crate::BitReader;
#[doc = "Field `IEPNEEN` writer - IN endpoint NAK effective interrupt enable bit"]
pub type IepneenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `NAKEN` reader - Interrupt enable bit of NAK handshake sent by USBHS"]
pub type NakenR = crate::BitReader;
#[doc = "Field `NAKEN` writer - Interrupt enable bit of NAK handshake sent by USBHS"]
pub type NakenW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Transfer finished interrupt enable bit"]
    #[inline(always)]
    pub fn tfen(&self) -> TfenR {
        TfenR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Endpoint disabled interrupt enable bit"]
    #[inline(always)]
    pub fn epdisen(&self) -> EpdisenR {
        EpdisenR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 3 - Control In Timeout interrupt enable bit"]
    #[inline(always)]
    pub fn citoen(&self) -> CitoenR {
        CitoenR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Endpoint Tx FIFO underrun interrupt enable bit"]
    #[inline(always)]
    pub fn eptxfuden(&self) -> EptxfudenR {
        EptxfudenR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 6 - IN endpoint NAK effective interrupt enable bit"]
    #[inline(always)]
    pub fn iepneen(&self) -> IepneenR {
        IepneenR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 13 - Interrupt enable bit of NAK handshake sent by USBHS"]
    #[inline(always)]
    pub fn naken(&self) -> NakenR {
        NakenR::new(((self.bits >> 13) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Transfer finished interrupt enable bit"]
    #[inline(always)]
    #[must_use]
    pub fn tfen(&mut self) -> TfenW<Diep1intenSpec> {
        TfenW::new(self, 0)
    }
    #[doc = "Bit 1 - Endpoint disabled interrupt enable bit"]
    #[inline(always)]
    #[must_use]
    pub fn epdisen(&mut self) -> EpdisenW<Diep1intenSpec> {
        EpdisenW::new(self, 1)
    }
    #[doc = "Bit 3 - Control In Timeout interrupt enable bit"]
    #[inline(always)]
    #[must_use]
    pub fn citoen(&mut self) -> CitoenW<Diep1intenSpec> {
        CitoenW::new(self, 3)
    }
    #[doc = "Bit 4 - Endpoint Tx FIFO underrun interrupt enable bit"]
    #[inline(always)]
    #[must_use]
    pub fn eptxfuden(&mut self) -> EptxfudenW<Diep1intenSpec> {
        EptxfudenW::new(self, 4)
    }
    #[doc = "Bit 6 - IN endpoint NAK effective interrupt enable bit"]
    #[inline(always)]
    #[must_use]
    pub fn iepneen(&mut self) -> IepneenW<Diep1intenSpec> {
        IepneenW::new(self, 6)
    }
    #[doc = "Bit 13 - Interrupt enable bit of NAK handshake sent by USBHS"]
    #[inline(always)]
    #[must_use]
    pub fn naken(&mut self) -> NakenW<Diep1intenSpec> {
        NakenW::new(self, 13)
    }
}
#[doc = "Device IN endpoint 1 interrupt enable register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diep1inten::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diep1inten::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Diep1intenSpec;
impl crate::RegisterSpec for Diep1intenSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`diep1inten::R`](R) reader structure"]
impl crate::Readable for Diep1intenSpec {}
#[doc = "`write(|w| ..)` method takes [`diep1inten::W`](W) writer structure"]
impl crate::Writable for Diep1intenSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DIEP1INTEN to value 0"]
impl crate::Resettable for Diep1intenSpec {
    const RESET_VALUE: u32 = 0;
}
