#[doc = "Register `GINTEN` reader"]
pub type R = crate::R<GintenSpec>;
#[doc = "Register `GINTEN` writer"]
pub type W = crate::W<GintenSpec>;
#[doc = "Field `MFIE` reader - Mode fault interrupt enable"]
pub type MfieR = crate::BitReader;
#[doc = "Field `MFIE` writer - Mode fault interrupt enable"]
pub type MfieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `OTGIE` reader - OTG interrupt enable"]
pub type OtgieR = crate::BitReader;
#[doc = "Field `OTGIE` writer - OTG interrupt enable"]
pub type OtgieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SOFIE` reader - Start of frame interrupt enable"]
pub type SofieR = crate::BitReader;
#[doc = "Field `SOFIE` writer - Start of frame interrupt enable"]
pub type SofieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RXFNEIE` reader - Receive FIFO non-empty interrupt enable"]
pub type RxfneieR = crate::BitReader;
#[doc = "Field `RXFNEIE` writer - Receive FIFO non-empty interrupt enable"]
pub type RxfneieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `NPTXFEIE` reader - Non-periodic TxFIFO empty interrupt enable"]
pub type NptxfeieR = crate::BitReader;
#[doc = "Field `NPTXFEIE` writer - Non-periodic TxFIFO empty interrupt enable"]
pub type NptxfeieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `GNPINAKIE` reader - Global non-periodic IN NAK effective interrupt enable"]
pub type GnpinakieR = crate::BitReader;
#[doc = "Field `GNPINAKIE` writer - Global non-periodic IN NAK effective interrupt enable"]
pub type GnpinakieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `GONAKIE` reader - Global OUT NAK effective interrupt enable"]
pub type GonakieR = crate::BitReader;
#[doc = "Field `GONAKIE` writer - Global OUT NAK effective interrupt enable"]
pub type GonakieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ESPIE` reader - Early suspend interrupt enable"]
pub type EspieR = crate::BitReader;
#[doc = "Field `ESPIE` writer - Early suspend interrupt enable"]
pub type EspieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPIE` reader - USB suspend interrupt enable"]
pub type SpieR = crate::BitReader;
#[doc = "Field `SPIE` writer - USB suspend interrupt enable"]
pub type SpieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RSTIE` reader - USB reset interrupt enable"]
pub type RstieR = crate::BitReader;
#[doc = "Field `RSTIE` writer - USB reset interrupt enable"]
pub type RstieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ENUMFIE` reader - Enumeration finish interrupt enable"]
pub type EnumfieR = crate::BitReader;
#[doc = "Field `ENUMFIE` writer - Enumeration finish interrupt enable"]
pub type EnumfieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ISOOPDIE` reader - Isochronous OUT packet dropped interrupt enable"]
pub type IsoopdieR = crate::BitReader;
#[doc = "Field `ISOOPDIE` writer - Isochronous OUT packet dropped interrupt enable"]
pub type IsoopdieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EOPFIE` reader - End of periodic frame interrupt enable"]
pub type EopfieR = crate::BitReader;
#[doc = "Field `EOPFIE` writer - End of periodic frame interrupt enable"]
pub type EopfieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IEPIE` reader - IN endpoints interrupt enable"]
pub type IepieR = crate::BitReader;
#[doc = "Field `IEPIE` writer - IN endpoints interrupt enable"]
pub type IepieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `OEPIE` reader - OUT endpoints interrupt enable"]
pub type OepieR = crate::BitReader;
#[doc = "Field `OEPIE` writer - OUT endpoints interrupt enable"]
pub type OepieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ISOINCIE` reader - isochronous IN transfer not complete interrupt enable"]
pub type IsoincieR = crate::BitReader;
#[doc = "Field `ISOINCIE` writer - isochronous IN transfer not complete interrupt enable"]
pub type IsoincieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PXNCIE_ISOONCIE` reader - periodic transfer not compelete Interrupt enable(Host mode)/isochronous OUT transfer not complete interrupt enable(Device mode)"]
pub type PxncieIsooncieR = crate::BitReader;
#[doc = "Field `PXNCIE_ISOONCIE` writer - periodic transfer not compelete Interrupt enable(Host mode)/isochronous OUT transfer not complete interrupt enable(Device mode)"]
pub type PxncieIsooncieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HPIE` reader - Host port interrupt enable"]
pub type HpieR = crate::BitReader;
#[doc = "Field `HCIE` reader - Host channels interrupt enable"]
pub type HcieR = crate::BitReader;
#[doc = "Field `HCIE` writer - Host channels interrupt enable"]
pub type HcieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PTXFEIE` reader - Periodic TxFIFO empty interrupt enable"]
pub type PtxfeieR = crate::BitReader;
#[doc = "Field `PTXFEIE` writer - Periodic TxFIFO empty interrupt enable"]
pub type PtxfeieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LPMIE` reader - LPM interrupt enable"]
pub type LpmieR = crate::BitReader;
#[doc = "Field `LPMIE` writer - LPM interrupt enable"]
pub type LpmieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IDPSCIE` reader - ID pin status change interrupt enable"]
pub type IdpscieR = crate::BitReader;
#[doc = "Field `IDPSCIE` writer - ID pin status change interrupt enable"]
pub type IdpscieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DISCIE` reader - Disconnect interrupt enable"]
pub type DiscieR = crate::BitReader;
#[doc = "Field `DISCIE` writer - Disconnect interrupt enable"]
pub type DiscieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SESIE` reader - Session interrupt enable"]
pub type SesieR = crate::BitReader;
#[doc = "Field `SESIE` writer - Session interrupt enable"]
pub type SesieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WKUPIE` reader - Wakeup interrupt enable"]
pub type WkupieR = crate::BitReader;
#[doc = "Field `WKUPIE` writer - Wakeup interrupt enable"]
pub type WkupieW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 1 - Mode fault interrupt enable"]
    #[inline(always)]
    pub fn mfie(&self) -> MfieR {
        MfieR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - OTG interrupt enable"]
    #[inline(always)]
    pub fn otgie(&self) -> OtgieR {
        OtgieR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Start of frame interrupt enable"]
    #[inline(always)]
    pub fn sofie(&self) -> SofieR {
        SofieR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Receive FIFO non-empty interrupt enable"]
    #[inline(always)]
    pub fn rxfneie(&self) -> RxfneieR {
        RxfneieR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Non-periodic TxFIFO empty interrupt enable"]
    #[inline(always)]
    pub fn nptxfeie(&self) -> NptxfeieR {
        NptxfeieR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Global non-periodic IN NAK effective interrupt enable"]
    #[inline(always)]
    pub fn gnpinakie(&self) -> GnpinakieR {
        GnpinakieR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Global OUT NAK effective interrupt enable"]
    #[inline(always)]
    pub fn gonakie(&self) -> GonakieR {
        GonakieR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 10 - Early suspend interrupt enable"]
    #[inline(always)]
    pub fn espie(&self) -> EspieR {
        EspieR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - USB suspend interrupt enable"]
    #[inline(always)]
    pub fn spie(&self) -> SpieR {
        SpieR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - USB reset interrupt enable"]
    #[inline(always)]
    pub fn rstie(&self) -> RstieR {
        RstieR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Enumeration finish interrupt enable"]
    #[inline(always)]
    pub fn enumfie(&self) -> EnumfieR {
        EnumfieR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Isochronous OUT packet dropped interrupt enable"]
    #[inline(always)]
    pub fn isoopdie(&self) -> IsoopdieR {
        IsoopdieR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - End of periodic frame interrupt enable"]
    #[inline(always)]
    pub fn eopfie(&self) -> EopfieR {
        EopfieR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 18 - IN endpoints interrupt enable"]
    #[inline(always)]
    pub fn iepie(&self) -> IepieR {
        IepieR::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - OUT endpoints interrupt enable"]
    #[inline(always)]
    pub fn oepie(&self) -> OepieR {
        OepieR::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - isochronous IN transfer not complete interrupt enable"]
    #[inline(always)]
    pub fn isoincie(&self) -> IsoincieR {
        IsoincieR::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - periodic transfer not compelete Interrupt enable(Host mode)/isochronous OUT transfer not complete interrupt enable(Device mode)"]
    #[inline(always)]
    pub fn pxncie_isooncie(&self) -> PxncieIsooncieR {
        PxncieIsooncieR::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 24 - Host port interrupt enable"]
    #[inline(always)]
    pub fn hpie(&self) -> HpieR {
        HpieR::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - Host channels interrupt enable"]
    #[inline(always)]
    pub fn hcie(&self) -> HcieR {
        HcieR::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - Periodic TxFIFO empty interrupt enable"]
    #[inline(always)]
    pub fn ptxfeie(&self) -> PtxfeieR {
        PtxfeieR::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - LPM interrupt enable"]
    #[inline(always)]
    pub fn lpmie(&self) -> LpmieR {
        LpmieR::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - ID pin status change interrupt enable"]
    #[inline(always)]
    pub fn idpscie(&self) -> IdpscieR {
        IdpscieR::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - Disconnect interrupt enable"]
    #[inline(always)]
    pub fn discie(&self) -> DiscieR {
        DiscieR::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - Session interrupt enable"]
    #[inline(always)]
    pub fn sesie(&self) -> SesieR {
        SesieR::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - Wakeup interrupt enable"]
    #[inline(always)]
    pub fn wkupie(&self) -> WkupieR {
        WkupieR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 1 - Mode fault interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn mfie(&mut self) -> MfieW<GintenSpec> {
        MfieW::new(self, 1)
    }
    #[doc = "Bit 2 - OTG interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn otgie(&mut self) -> OtgieW<GintenSpec> {
        OtgieW::new(self, 2)
    }
    #[doc = "Bit 3 - Start of frame interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn sofie(&mut self) -> SofieW<GintenSpec> {
        SofieW::new(self, 3)
    }
    #[doc = "Bit 4 - Receive FIFO non-empty interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn rxfneie(&mut self) -> RxfneieW<GintenSpec> {
        RxfneieW::new(self, 4)
    }
    #[doc = "Bit 5 - Non-periodic TxFIFO empty interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn nptxfeie(&mut self) -> NptxfeieW<GintenSpec> {
        NptxfeieW::new(self, 5)
    }
    #[doc = "Bit 6 - Global non-periodic IN NAK effective interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn gnpinakie(&mut self) -> GnpinakieW<GintenSpec> {
        GnpinakieW::new(self, 6)
    }
    #[doc = "Bit 7 - Global OUT NAK effective interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn gonakie(&mut self) -> GonakieW<GintenSpec> {
        GonakieW::new(self, 7)
    }
    #[doc = "Bit 10 - Early suspend interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn espie(&mut self) -> EspieW<GintenSpec> {
        EspieW::new(self, 10)
    }
    #[doc = "Bit 11 - USB suspend interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn spie(&mut self) -> SpieW<GintenSpec> {
        SpieW::new(self, 11)
    }
    #[doc = "Bit 12 - USB reset interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn rstie(&mut self) -> RstieW<GintenSpec> {
        RstieW::new(self, 12)
    }
    #[doc = "Bit 13 - Enumeration finish interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn enumfie(&mut self) -> EnumfieW<GintenSpec> {
        EnumfieW::new(self, 13)
    }
    #[doc = "Bit 14 - Isochronous OUT packet dropped interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn isoopdie(&mut self) -> IsoopdieW<GintenSpec> {
        IsoopdieW::new(self, 14)
    }
    #[doc = "Bit 15 - End of periodic frame interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn eopfie(&mut self) -> EopfieW<GintenSpec> {
        EopfieW::new(self, 15)
    }
    #[doc = "Bit 18 - IN endpoints interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn iepie(&mut self) -> IepieW<GintenSpec> {
        IepieW::new(self, 18)
    }
    #[doc = "Bit 19 - OUT endpoints interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn oepie(&mut self) -> OepieW<GintenSpec> {
        OepieW::new(self, 19)
    }
    #[doc = "Bit 20 - isochronous IN transfer not complete interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn isoincie(&mut self) -> IsoincieW<GintenSpec> {
        IsoincieW::new(self, 20)
    }
    #[doc = "Bit 21 - periodic transfer not compelete Interrupt enable(Host mode)/isochronous OUT transfer not complete interrupt enable(Device mode)"]
    #[inline(always)]
    #[must_use]
    pub fn pxncie_isooncie(&mut self) -> PxncieIsooncieW<GintenSpec> {
        PxncieIsooncieW::new(self, 21)
    }
    #[doc = "Bit 25 - Host channels interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn hcie(&mut self) -> HcieW<GintenSpec> {
        HcieW::new(self, 25)
    }
    #[doc = "Bit 26 - Periodic TxFIFO empty interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn ptxfeie(&mut self) -> PtxfeieW<GintenSpec> {
        PtxfeieW::new(self, 26)
    }
    #[doc = "Bit 27 - LPM interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn lpmie(&mut self) -> LpmieW<GintenSpec> {
        LpmieW::new(self, 27)
    }
    #[doc = "Bit 28 - ID pin status change interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn idpscie(&mut self) -> IdpscieW<GintenSpec> {
        IdpscieW::new(self, 28)
    }
    #[doc = "Bit 29 - Disconnect interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn discie(&mut self) -> DiscieW<GintenSpec> {
        DiscieW::new(self, 29)
    }
    #[doc = "Bit 30 - Session interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn sesie(&mut self) -> SesieW<GintenSpec> {
        SesieW::new(self, 30)
    }
    #[doc = "Bit 31 - Wakeup interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn wkupie(&mut self) -> WkupieW<GintenSpec> {
        WkupieW::new(self, 31)
    }
}
#[doc = "Global interrupt enable register (USBHS_GINTEN)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ginten::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ginten::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct GintenSpec;
impl crate::RegisterSpec for GintenSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ginten::R`](R) reader structure"]
impl crate::Readable for GintenSpec {}
#[doc = "`write(|w| ..)` method takes [`ginten::W`](W) writer structure"]
impl crate::Writable for GintenSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets GINTEN to value 0"]
impl crate::Resettable for GintenSpec {
    const RESET_VALUE: u32 = 0;
}
