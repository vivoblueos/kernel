#[doc = "Register `INTEN` reader"]
pub type R = crate::R<IntenSpec>;
#[doc = "Register `INTEN` writer"]
pub type W = crate::W<IntenSpec>;
#[doc = "Field `CCRCERRIE` reader - Command response CRC fail interrupt enable"]
pub type CcrcerrieR = crate::BitReader;
#[doc = "Field `CCRCERRIE` writer - Command response CRC fail interrupt enable"]
pub type CcrcerrieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DTCRCERRIE` reader - Data CRC fail interrupt enable"]
pub type DtcrcerrieR = crate::BitReader;
#[doc = "Field `DTCRCERRIE` writer - Data CRC fail interrupt enable"]
pub type DtcrcerrieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMDTMOUTIE` reader - Command response timeout interrupt enable"]
pub type CmdtmoutieR = crate::BitReader;
#[doc = "Field `CMDTMOUTIE` writer - Command response timeout interrupt enable"]
pub type CmdtmoutieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DTTMOUTIE` reader - Data timeout interrupt enable"]
pub type DttmoutieR = crate::BitReader;
#[doc = "Field `DTTMOUTIE` writer - Data timeout interrupt enable"]
pub type DttmoutieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TXUREIE` reader - Transmit FIFO underrun error interrupt enable"]
pub type TxureieR = crate::BitReader;
#[doc = "Field `TXUREIE` writer - Transmit FIFO underrun error interrupt enable"]
pub type TxureieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RXOREIE` reader - Received FIFO overrun error interrupt enable"]
pub type RxoreieR = crate::BitReader;
#[doc = "Field `RXOREIE` writer - Received FIFO overrun error interrupt enable"]
pub type RxoreieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMDRECVIE` reader - Command response received interrupt enable"]
pub type CmdrecvieR = crate::BitReader;
#[doc = "Field `CMDRECVIE` writer - Command response received interrupt enable"]
pub type CmdrecvieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMDSENDIE` reader - Command sent interrupt enable"]
pub type CmdsendieR = crate::BitReader;
#[doc = "Field `CMDSENDIE` writer - Command sent interrupt enable"]
pub type CmdsendieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DTENDIE` reader - Data end interrupt enable"]
pub type DtendieR = crate::BitReader;
#[doc = "Field `DTENDIE` writer - Data end interrupt enable"]
pub type DtendieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `STBITEIE` reader - Start bit error interrupt enable"]
pub type StbiteieR = crate::BitReader;
#[doc = "Field `STBITEIE` writer - Start bit error interrupt enable"]
pub type StbiteieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `DTBLKENDIE` reader - Data block end interrupt enable"]
pub type DtblkendieR = crate::BitReader;
#[doc = "Field `DTBLKENDIE` writer - Data block end interrupt enable"]
pub type DtblkendieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CMDRUNIE` reader - Command transmission interrupt enable"]
pub type CmdrunieR = crate::BitReader;
#[doc = "Field `CMDRUNIE` writer - Command transmission interrupt enable"]
pub type CmdrunieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TXRUNIE` reader - Data transmission interrupt enable"]
pub type TxrunieR = crate::BitReader;
#[doc = "Field `TXRUNIE` writer - Data transmission interrupt enable"]
pub type TxrunieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RXRUNIE` reader - Data reception interrupt enable"]
pub type RxrunieR = crate::BitReader;
#[doc = "Field `RXRUNIE` writer - Data reception interrupt enable"]
pub type RxrunieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TFHIE` reader - Transmit FIFO half empty interrupt enable"]
pub type TfhieR = crate::BitReader;
#[doc = "Field `TFHIE` writer - Transmit FIFO half empty interrupt enable"]
pub type TfhieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RFHIE` reader - Receive FIFO half full interrupt enable"]
pub type RfhieR = crate::BitReader;
#[doc = "Field `RFHIE` writer - Receive FIFO half full interrupt enable"]
pub type RfhieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TFFIE` reader - Transmit FIFO full interrupt enable"]
pub type TffieR = crate::BitReader;
#[doc = "Field `TFFIE` writer - Transmit FIFO full interrupt enable"]
pub type TffieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RFFIE` reader - Receive FIFO full interrupt enable"]
pub type RffieR = crate::BitReader;
#[doc = "Field `RFFIE` writer - Receive FIFO full interrupt enable"]
pub type RffieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TFEIE` reader - Transmit FIFO empty interrupt enable"]
pub type TfeieR = crate::BitReader;
#[doc = "Field `TFEIE` writer - Transmit FIFO empty interrupt enable"]
pub type TfeieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RFEIE` reader - Receive FIFO empty interrupt enable"]
pub type RfeieR = crate::BitReader;
#[doc = "Field `RFEIE` writer - Receive FIFO empty interrupt enable"]
pub type RfeieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TXDTVALIE` reader - Data valid in transmit FIFO interrupt enable"]
pub type TxdtvalieR = crate::BitReader;
#[doc = "Field `TXDTVALIE` writer - Data valid in transmit FIFO interrupt enable"]
pub type TxdtvalieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RXDTVALIE` reader - Data valid in receive FIFO interrupt enable"]
pub type RxdtvalieR = crate::BitReader;
#[doc = "Field `RXDTVALIE` writer - Data valid in receive FIFO interrupt enable"]
pub type RxdtvalieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SDIOINTIE` reader - SD I/O interrupt received interrupt enable"]
pub type SdiointieR = crate::BitReader;
#[doc = "Field `SDIOINTIE` writer - SD I/O interrupt received interrupt enable"]
pub type SdiointieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ATAENDIE` reader - CE-ATA command completion signal received interrupt enable"]
pub type AtaendieR = crate::BitReader;
#[doc = "Field `ATAENDIE` writer - CE-ATA command completion signal received interrupt enable"]
pub type AtaendieW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Command response CRC fail interrupt enable"]
    #[inline(always)]
    pub fn ccrcerrie(&self) -> CcrcerrieR {
        CcrcerrieR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Data CRC fail interrupt enable"]
    #[inline(always)]
    pub fn dtcrcerrie(&self) -> DtcrcerrieR {
        DtcrcerrieR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Command response timeout interrupt enable"]
    #[inline(always)]
    pub fn cmdtmoutie(&self) -> CmdtmoutieR {
        CmdtmoutieR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Data timeout interrupt enable"]
    #[inline(always)]
    pub fn dttmoutie(&self) -> DttmoutieR {
        DttmoutieR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Transmit FIFO underrun error interrupt enable"]
    #[inline(always)]
    pub fn txureie(&self) -> TxureieR {
        TxureieR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Received FIFO overrun error interrupt enable"]
    #[inline(always)]
    pub fn rxoreie(&self) -> RxoreieR {
        RxoreieR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Command response received interrupt enable"]
    #[inline(always)]
    pub fn cmdrecvie(&self) -> CmdrecvieR {
        CmdrecvieR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Command sent interrupt enable"]
    #[inline(always)]
    pub fn cmdsendie(&self) -> CmdsendieR {
        CmdsendieR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Data end interrupt enable"]
    #[inline(always)]
    pub fn dtendie(&self) -> DtendieR {
        DtendieR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Start bit error interrupt enable"]
    #[inline(always)]
    pub fn stbiteie(&self) -> StbiteieR {
        StbiteieR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Data block end interrupt enable"]
    #[inline(always)]
    pub fn dtblkendie(&self) -> DtblkendieR {
        DtblkendieR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Command transmission interrupt enable"]
    #[inline(always)]
    pub fn cmdrunie(&self) -> CmdrunieR {
        CmdrunieR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Data transmission interrupt enable"]
    #[inline(always)]
    pub fn txrunie(&self) -> TxrunieR {
        TxrunieR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Data reception interrupt enable"]
    #[inline(always)]
    pub fn rxrunie(&self) -> RxrunieR {
        RxrunieR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Transmit FIFO half empty interrupt enable"]
    #[inline(always)]
    pub fn tfhie(&self) -> TfhieR {
        TfhieR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Receive FIFO half full interrupt enable"]
    #[inline(always)]
    pub fn rfhie(&self) -> RfhieR {
        RfhieR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - Transmit FIFO full interrupt enable"]
    #[inline(always)]
    pub fn tffie(&self) -> TffieR {
        TffieR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - Receive FIFO full interrupt enable"]
    #[inline(always)]
    pub fn rffie(&self) -> RffieR {
        RffieR::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - Transmit FIFO empty interrupt enable"]
    #[inline(always)]
    pub fn tfeie(&self) -> TfeieR {
        TfeieR::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - Receive FIFO empty interrupt enable"]
    #[inline(always)]
    pub fn rfeie(&self) -> RfeieR {
        RfeieR::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - Data valid in transmit FIFO interrupt enable"]
    #[inline(always)]
    pub fn txdtvalie(&self) -> TxdtvalieR {
        TxdtvalieR::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - Data valid in receive FIFO interrupt enable"]
    #[inline(always)]
    pub fn rxdtvalie(&self) -> RxdtvalieR {
        RxdtvalieR::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 22 - SD I/O interrupt received interrupt enable"]
    #[inline(always)]
    pub fn sdiointie(&self) -> SdiointieR {
        SdiointieR::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 23 - CE-ATA command completion signal received interrupt enable"]
    #[inline(always)]
    pub fn ataendie(&self) -> AtaendieR {
        AtaendieR::new(((self.bits >> 23) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Command response CRC fail interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn ccrcerrie(&mut self) -> CcrcerrieW<IntenSpec> {
        CcrcerrieW::new(self, 0)
    }
    #[doc = "Bit 1 - Data CRC fail interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn dtcrcerrie(&mut self) -> DtcrcerrieW<IntenSpec> {
        DtcrcerrieW::new(self, 1)
    }
    #[doc = "Bit 2 - Command response timeout interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn cmdtmoutie(&mut self) -> CmdtmoutieW<IntenSpec> {
        CmdtmoutieW::new(self, 2)
    }
    #[doc = "Bit 3 - Data timeout interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn dttmoutie(&mut self) -> DttmoutieW<IntenSpec> {
        DttmoutieW::new(self, 3)
    }
    #[doc = "Bit 4 - Transmit FIFO underrun error interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn txureie(&mut self) -> TxureieW<IntenSpec> {
        TxureieW::new(self, 4)
    }
    #[doc = "Bit 5 - Received FIFO overrun error interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn rxoreie(&mut self) -> RxoreieW<IntenSpec> {
        RxoreieW::new(self, 5)
    }
    #[doc = "Bit 6 - Command response received interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn cmdrecvie(&mut self) -> CmdrecvieW<IntenSpec> {
        CmdrecvieW::new(self, 6)
    }
    #[doc = "Bit 7 - Command sent interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn cmdsendie(&mut self) -> CmdsendieW<IntenSpec> {
        CmdsendieW::new(self, 7)
    }
    #[doc = "Bit 8 - Data end interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn dtendie(&mut self) -> DtendieW<IntenSpec> {
        DtendieW::new(self, 8)
    }
    #[doc = "Bit 9 - Start bit error interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn stbiteie(&mut self) -> StbiteieW<IntenSpec> {
        StbiteieW::new(self, 9)
    }
    #[doc = "Bit 10 - Data block end interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn dtblkendie(&mut self) -> DtblkendieW<IntenSpec> {
        DtblkendieW::new(self, 10)
    }
    #[doc = "Bit 11 - Command transmission interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn cmdrunie(&mut self) -> CmdrunieW<IntenSpec> {
        CmdrunieW::new(self, 11)
    }
    #[doc = "Bit 12 - Data transmission interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn txrunie(&mut self) -> TxrunieW<IntenSpec> {
        TxrunieW::new(self, 12)
    }
    #[doc = "Bit 13 - Data reception interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn rxrunie(&mut self) -> RxrunieW<IntenSpec> {
        RxrunieW::new(self, 13)
    }
    #[doc = "Bit 14 - Transmit FIFO half empty interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn tfhie(&mut self) -> TfhieW<IntenSpec> {
        TfhieW::new(self, 14)
    }
    #[doc = "Bit 15 - Receive FIFO half full interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn rfhie(&mut self) -> RfhieW<IntenSpec> {
        RfhieW::new(self, 15)
    }
    #[doc = "Bit 16 - Transmit FIFO full interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn tffie(&mut self) -> TffieW<IntenSpec> {
        TffieW::new(self, 16)
    }
    #[doc = "Bit 17 - Receive FIFO full interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn rffie(&mut self) -> RffieW<IntenSpec> {
        RffieW::new(self, 17)
    }
    #[doc = "Bit 18 - Transmit FIFO empty interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn tfeie(&mut self) -> TfeieW<IntenSpec> {
        TfeieW::new(self, 18)
    }
    #[doc = "Bit 19 - Receive FIFO empty interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn rfeie(&mut self) -> RfeieW<IntenSpec> {
        RfeieW::new(self, 19)
    }
    #[doc = "Bit 20 - Data valid in transmit FIFO interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn txdtvalie(&mut self) -> TxdtvalieW<IntenSpec> {
        TxdtvalieW::new(self, 20)
    }
    #[doc = "Bit 21 - Data valid in receive FIFO interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn rxdtvalie(&mut self) -> RxdtvalieW<IntenSpec> {
        RxdtvalieW::new(self, 21)
    }
    #[doc = "Bit 22 - SD I/O interrupt received interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn sdiointie(&mut self) -> SdiointieW<IntenSpec> {
        SdiointieW::new(self, 22)
    }
    #[doc = "Bit 23 - CE-ATA command completion signal received interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn ataendie(&mut self) -> AtaendieW<IntenSpec> {
        AtaendieW::new(self, 23)
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
