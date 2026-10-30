#[doc = "Register `GINTF` reader"]
pub type R = crate::R<GintfSpec>;
#[doc = "Register `GINTF` writer"]
pub type W = crate::W<GintfSpec>;
#[doc = "Field `COPM` reader - Current operation mode"]
pub type CopmR = crate::BitReader;
#[doc = "Field `MFIF` reader - Mode fault interrupt flag"]
pub type MfifR = crate::BitReader;
#[doc = "Field `MFIF` writer - Mode fault interrupt flag"]
pub type MfifW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `OTGIF` reader - OTG interrupt flag"]
pub type OtgifR = crate::BitReader;
#[doc = "Field `SOF` reader - Start of frame"]
pub type SofR = crate::BitReader;
#[doc = "Field `SOF` writer - Start of frame"]
pub type SofW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RXFNEIF` reader - RxFIFO non-empty interrupt flag"]
pub type RxfneifR = crate::BitReader;
#[doc = "Field `NPTXFEIF` reader - Non-periodic TxFIFO empty interrupt flag"]
pub type NptxfeifR = crate::BitReader;
#[doc = "Field `GNPINAK` reader - Global Non-Periodic IN NAK effective"]
pub type GnpinakR = crate::BitReader;
#[doc = "Field `GONAK` reader - Global OUT NAK effective"]
pub type GonakR = crate::BitReader;
#[doc = "Field `ESP` reader - Early suspend"]
pub type EspR = crate::BitReader;
#[doc = "Field `ESP` writer - Early suspend"]
pub type EspW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SP` reader - USB suspend"]
pub type SpR = crate::BitReader;
#[doc = "Field `SP` writer - USB suspend"]
pub type SpW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RST` reader - USB reset"]
pub type RstR = crate::BitReader;
#[doc = "Field `RST` writer - USB reset"]
pub type RstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ENUMF` reader - Enumeration finished"]
pub type EnumfR = crate::BitReader;
#[doc = "Field `ENUMF` writer - Enumeration finished"]
pub type EnumfW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ISOOPDIF` reader - Isochronous OUT packet dropped interrupt"]
pub type IsoopdifR = crate::BitReader;
#[doc = "Field `ISOOPDIF` writer - Isochronous OUT packet dropped interrupt"]
pub type IsoopdifW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EOPFIF` reader - End of periodic frame interrupt flag"]
pub type EopfifR = crate::BitReader;
#[doc = "Field `EOPFIF` writer - End of periodic frame interrupt flag"]
pub type EopfifW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IEPIF` reader - IN endpoint interrupt flag"]
pub type IepifR = crate::BitReader;
#[doc = "Field `OEPIF` reader - OUT endpoint interrupt flag"]
pub type OepifR = crate::BitReader;
#[doc = "Field `ISOINCIF` reader - Isochronous IN transfer Not Complete Interrupt Flag"]
pub type IsoincifR = crate::BitReader;
#[doc = "Field `ISOINCIF` writer - Isochronous IN transfer Not Complete Interrupt Flag"]
pub type IsoincifW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PXNCIF_ISOONCIF` reader - periodic transfer not complete interrupt flag(Host mode)/isochronous OUT transfer not complete interrupt flag(Device mode)"]
pub type PxncifIsooncifR = crate::BitReader;
#[doc = "Field `PXNCIF_ISOONCIF` writer - periodic transfer not complete interrupt flag(Host mode)/isochronous OUT transfer not complete interrupt flag(Device mode)"]
pub type PxncifIsooncifW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `HPIF` reader - Host port interrupt flag"]
pub type HpifR = crate::BitReader;
#[doc = "Field `HCIF` reader - Host channels interrupt flag"]
pub type HcifR = crate::BitReader;
#[doc = "Field `PTXFEIF` reader - Periodic TxFIFO empty interrupt flag"]
pub type PtxfeifR = crate::BitReader;
#[doc = "Field `LPMIF` reader - LPM interrupt flag"]
pub type LpmifR = crate::BitReader;
#[doc = "Field `LPMIF` writer - LPM interrupt flag"]
pub type LpmifW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IDPSC` reader - ID pin status change"]
pub type IdpscR = crate::BitReader;
#[doc = "Field `IDPSC` writer - ID pin status change"]
pub type IdpscW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DISCIF` reader - Disconnect interrupt flag"]
pub type DiscifR = crate::BitReader;
#[doc = "Field `DISCIF` writer - Disconnect interrupt flag"]
pub type DiscifW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SESIF` reader - Session interrupt flag"]
pub type SesifR = crate::BitReader;
#[doc = "Field `SESIF` writer - Session interrupt flag"]
pub type SesifW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WKUPIF` reader - Wakeup interrupt flag"]
pub type WkupifR = crate::BitReader;
#[doc = "Field `WKUPIF` writer - Wakeup interrupt flag"]
pub type WkupifW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Current operation mode"]
    #[inline(always)]
    pub fn copm(&self) -> CopmR {
        CopmR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Mode fault interrupt flag"]
    #[inline(always)]
    pub fn mfif(&self) -> MfifR {
        MfifR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - OTG interrupt flag"]
    #[inline(always)]
    pub fn otgif(&self) -> OtgifR {
        OtgifR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Start of frame"]
    #[inline(always)]
    pub fn sof(&self) -> SofR {
        SofR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - RxFIFO non-empty interrupt flag"]
    #[inline(always)]
    pub fn rxfneif(&self) -> RxfneifR {
        RxfneifR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Non-periodic TxFIFO empty interrupt flag"]
    #[inline(always)]
    pub fn nptxfeif(&self) -> NptxfeifR {
        NptxfeifR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Global Non-Periodic IN NAK effective"]
    #[inline(always)]
    pub fn gnpinak(&self) -> GnpinakR {
        GnpinakR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Global OUT NAK effective"]
    #[inline(always)]
    pub fn gonak(&self) -> GonakR {
        GonakR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 10 - Early suspend"]
    #[inline(always)]
    pub fn esp(&self) -> EspR {
        EspR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - USB suspend"]
    #[inline(always)]
    pub fn sp(&self) -> SpR {
        SpR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - USB reset"]
    #[inline(always)]
    pub fn rst(&self) -> RstR {
        RstR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Enumeration finished"]
    #[inline(always)]
    pub fn enumf(&self) -> EnumfR {
        EnumfR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Isochronous OUT packet dropped interrupt"]
    #[inline(always)]
    pub fn isoopdif(&self) -> IsoopdifR {
        IsoopdifR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - End of periodic frame interrupt flag"]
    #[inline(always)]
    pub fn eopfif(&self) -> EopfifR {
        EopfifR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 18 - IN endpoint interrupt flag"]
    #[inline(always)]
    pub fn iepif(&self) -> IepifR {
        IepifR::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - OUT endpoint interrupt flag"]
    #[inline(always)]
    pub fn oepif(&self) -> OepifR {
        OepifR::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - Isochronous IN transfer Not Complete Interrupt Flag"]
    #[inline(always)]
    pub fn isoincif(&self) -> IsoincifR {
        IsoincifR::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - periodic transfer not complete interrupt flag(Host mode)/isochronous OUT transfer not complete interrupt flag(Device mode)"]
    #[inline(always)]
    pub fn pxncif_isooncif(&self) -> PxncifIsooncifR {
        PxncifIsooncifR::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 24 - Host port interrupt flag"]
    #[inline(always)]
    pub fn hpif(&self) -> HpifR {
        HpifR::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - Host channels interrupt flag"]
    #[inline(always)]
    pub fn hcif(&self) -> HcifR {
        HcifR::new(((self.bits >> 25) & 1) != 0)
    }
    #[doc = "Bit 26 - Periodic TxFIFO empty interrupt flag"]
    #[inline(always)]
    pub fn ptxfeif(&self) -> PtxfeifR {
        PtxfeifR::new(((self.bits >> 26) & 1) != 0)
    }
    #[doc = "Bit 27 - LPM interrupt flag"]
    #[inline(always)]
    pub fn lpmif(&self) -> LpmifR {
        LpmifR::new(((self.bits >> 27) & 1) != 0)
    }
    #[doc = "Bit 28 - ID pin status change"]
    #[inline(always)]
    pub fn idpsc(&self) -> IdpscR {
        IdpscR::new(((self.bits >> 28) & 1) != 0)
    }
    #[doc = "Bit 29 - Disconnect interrupt flag"]
    #[inline(always)]
    pub fn discif(&self) -> DiscifR {
        DiscifR::new(((self.bits >> 29) & 1) != 0)
    }
    #[doc = "Bit 30 - Session interrupt flag"]
    #[inline(always)]
    pub fn sesif(&self) -> SesifR {
        SesifR::new(((self.bits >> 30) & 1) != 0)
    }
    #[doc = "Bit 31 - Wakeup interrupt flag"]
    #[inline(always)]
    pub fn wkupif(&self) -> WkupifR {
        WkupifR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 1 - Mode fault interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn mfif(&mut self) -> MfifW<GintfSpec> {
        MfifW::new(self, 1)
    }
    #[doc = "Bit 3 - Start of frame"]
    #[inline(always)]
    #[must_use]
    pub fn sof(&mut self) -> SofW<GintfSpec> {
        SofW::new(self, 3)
    }
    #[doc = "Bit 10 - Early suspend"]
    #[inline(always)]
    #[must_use]
    pub fn esp(&mut self) -> EspW<GintfSpec> {
        EspW::new(self, 10)
    }
    #[doc = "Bit 11 - USB suspend"]
    #[inline(always)]
    #[must_use]
    pub fn sp(&mut self) -> SpW<GintfSpec> {
        SpW::new(self, 11)
    }
    #[doc = "Bit 12 - USB reset"]
    #[inline(always)]
    #[must_use]
    pub fn rst(&mut self) -> RstW<GintfSpec> {
        RstW::new(self, 12)
    }
    #[doc = "Bit 13 - Enumeration finished"]
    #[inline(always)]
    #[must_use]
    pub fn enumf(&mut self) -> EnumfW<GintfSpec> {
        EnumfW::new(self, 13)
    }
    #[doc = "Bit 14 - Isochronous OUT packet dropped interrupt"]
    #[inline(always)]
    #[must_use]
    pub fn isoopdif(&mut self) -> IsoopdifW<GintfSpec> {
        IsoopdifW::new(self, 14)
    }
    #[doc = "Bit 15 - End of periodic frame interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn eopfif(&mut self) -> EopfifW<GintfSpec> {
        EopfifW::new(self, 15)
    }
    #[doc = "Bit 20 - Isochronous IN transfer Not Complete Interrupt Flag"]
    #[inline(always)]
    #[must_use]
    pub fn isoincif(&mut self) -> IsoincifW<GintfSpec> {
        IsoincifW::new(self, 20)
    }
    #[doc = "Bit 21 - periodic transfer not complete interrupt flag(Host mode)/isochronous OUT transfer not complete interrupt flag(Device mode)"]
    #[inline(always)]
    #[must_use]
    pub fn pxncif_isooncif(&mut self) -> PxncifIsooncifW<GintfSpec> {
        PxncifIsooncifW::new(self, 21)
    }
    #[doc = "Bit 27 - LPM interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn lpmif(&mut self) -> LpmifW<GintfSpec> {
        LpmifW::new(self, 27)
    }
    #[doc = "Bit 28 - ID pin status change"]
    #[inline(always)]
    #[must_use]
    pub fn idpsc(&mut self) -> IdpscW<GintfSpec> {
        IdpscW::new(self, 28)
    }
    #[doc = "Bit 29 - Disconnect interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn discif(&mut self) -> DiscifW<GintfSpec> {
        DiscifW::new(self, 29)
    }
    #[doc = "Bit 30 - Session interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn sesif(&mut self) -> SesifW<GintfSpec> {
        SesifW::new(self, 30)
    }
    #[doc = "Bit 31 - Wakeup interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn wkupif(&mut self) -> WkupifW<GintfSpec> {
        WkupifW::new(self, 31)
    }
}
#[doc = "Global interrupt flag register (USBFS_GINTF)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`gintf::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`gintf::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct GintfSpec;
impl crate::RegisterSpec for GintfSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`gintf::R`](R) reader structure"]
impl crate::Readable for GintfSpec {}
#[doc = "`write(|w| ..)` method takes [`gintf::W`](W) writer structure"]
impl crate::Writable for GintfSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets GINTF to value 0x0400_0021"]
impl crate::Resettable for GintfSpec {
    const RESET_VALUE: u32 = 0x0400_0021;
}
