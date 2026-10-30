#[doc = "Register `DIEPINTEN` reader"]
pub type R = crate::R<DiepintenSpec>;
#[doc = "Register `DIEPINTEN` writer"]
pub type W = crate::W<DiepintenSpec>;
#[doc = "Field `TFEN` reader - Transfer finished interrupt enable"]
pub type TfenR = crate::BitReader;
#[doc = "Field `TFEN` writer - Transfer finished interrupt enable"]
pub type TfenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EPDISEN` reader - Endpoint disabled interrupt enable"]
pub type EpdisenR = crate::BitReader;
#[doc = "Field `EPDISEN` writer - Endpoint disabled interrupt enable"]
pub type EpdisenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CITOEN` reader - Control IN timeout condition interrupt enable (Non-isochronous endpoints)"]
pub type CitoenR = crate::BitReader;
#[doc = "Field `CITOEN` writer - Control IN timeout condition interrupt enable (Non-isochronous endpoints)"]
pub type CitoenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EPTXFUDEN` reader - Endpoint Tx FIFO underrun interrupt enable bit"]
pub type EptxfudenR = crate::BitReader;
#[doc = "Field `EPTXFUDEN` writer - Endpoint Tx FIFO underrun interrupt enable bit"]
pub type EptxfudenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IEPNEEN` reader - IN endpoint NAK effective interrupt enable"]
pub type IepneenR = crate::BitReader;
#[doc = "Field `IEPNEEN` writer - IN endpoint NAK effective interrupt enable"]
pub type IepneenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `NAKEN` reader - NAK handshake sent by USBHS interrupt enable bit"]
pub type NakenR = crate::BitReader;
#[doc = "Field `NAKEN` writer - NAK handshake sent by USBHS interrupt enable bit"]
pub type NakenW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Transfer finished interrupt enable"]
    #[inline(always)]
    pub fn tfen(&self) -> TfenR {
        TfenR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Endpoint disabled interrupt enable"]
    #[inline(always)]
    pub fn epdisen(&self) -> EpdisenR {
        EpdisenR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 3 - Control IN timeout condition interrupt enable (Non-isochronous endpoints)"]
    #[inline(always)]
    pub fn citoen(&self) -> CitoenR {
        CitoenR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Endpoint Tx FIFO underrun interrupt enable bit"]
    #[inline(always)]
    pub fn eptxfuden(&self) -> EptxfudenR {
        EptxfudenR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 6 - IN endpoint NAK effective interrupt enable"]
    #[inline(always)]
    pub fn iepneen(&self) -> IepneenR {
        IepneenR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 13 - NAK handshake sent by USBHS interrupt enable bit"]
    #[inline(always)]
    pub fn naken(&self) -> NakenR {
        NakenR::new(((self.bits >> 13) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Transfer finished interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn tfen(&mut self) -> TfenW<DiepintenSpec> {
        TfenW::new(self, 0)
    }
    #[doc = "Bit 1 - Endpoint disabled interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn epdisen(&mut self) -> EpdisenW<DiepintenSpec> {
        EpdisenW::new(self, 1)
    }
    #[doc = "Bit 3 - Control IN timeout condition interrupt enable (Non-isochronous endpoints)"]
    #[inline(always)]
    #[must_use]
    pub fn citoen(&mut self) -> CitoenW<DiepintenSpec> {
        CitoenW::new(self, 3)
    }
    #[doc = "Bit 4 - Endpoint Tx FIFO underrun interrupt enable bit"]
    #[inline(always)]
    #[must_use]
    pub fn eptxfuden(&mut self) -> EptxfudenW<DiepintenSpec> {
        EptxfudenW::new(self, 4)
    }
    #[doc = "Bit 6 - IN endpoint NAK effective interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn iepneen(&mut self) -> IepneenW<DiepintenSpec> {
        IepneenW::new(self, 6)
    }
    #[doc = "Bit 13 - NAK handshake sent by USBHS interrupt enable bit"]
    #[inline(always)]
    #[must_use]
    pub fn naken(&mut self) -> NakenW<DiepintenSpec> {
        NakenW::new(self, 13)
    }
}
#[doc = "device IN endpoint common interrupt mask register (DIEPINTEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`diepinten::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`diepinten::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct DiepintenSpec;
impl crate::RegisterSpec for DiepintenSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`diepinten::R`](R) reader structure"]
impl crate::Readable for DiepintenSpec {}
#[doc = "`write(|w| ..)` method takes [`diepinten::W`](W) writer structure"]
impl crate::Writable for DiepintenSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets DIEPINTEN to value 0"]
impl crate::Resettable for DiepintenSpec {
    const RESET_VALUE: u32 = 0;
}
