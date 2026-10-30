#[doc = "Register `STAT` reader"]
pub type R = crate::R<StatSpec>;
#[doc = "Field `CCRCERR` reader - Command response received"]
pub type CcrcerrR = crate::BitReader;
#[doc = "Field `DTCRCERR` reader - Data block sent/received"]
pub type DtcrcerrR = crate::BitReader;
#[doc = "Field `CMDTMOUT` reader - Command response timeout"]
pub type CmdtmoutR = crate::BitReader;
#[doc = "Field `DTTMOUT` reader - Data timeout"]
pub type DttmoutR = crate::BitReader;
#[doc = "Field `TXURE` reader - Transmit FIFO underrun error occurs"]
pub type TxureR = crate::BitReader;
#[doc = "Field `RXORE` reader - Received FIFO overrun error occurs"]
pub type RxoreR = crate::BitReader;
#[doc = "Field `CMDRECV` reader - Command response received"]
pub type CmdrecvR = crate::BitReader;
#[doc = "Field `CMDSEND` reader - Command sent"]
pub type CmdsendR = crate::BitReader;
#[doc = "Field `DTEND` reader - Data end"]
pub type DtendR = crate::BitReader;
#[doc = "Field `STBITE` reader - Start bit error in the bus"]
pub type StbiteR = crate::BitReader;
#[doc = "Field `DTBLKEND` reader - Data block sent/received"]
pub type DtblkendR = crate::BitReader;
#[doc = "Field `CMDRUN` reader - Command transmission in progress"]
pub type CmdrunR = crate::BitReader;
#[doc = "Field `TXRUN` reader - Data transmission in progress"]
pub type TxrunR = crate::BitReader;
#[doc = "Field `RXRUN` reader - Data reception in progress"]
pub type RxrunR = crate::BitReader;
#[doc = "Field `TFH` reader - Transmit FIFO is half empty"]
pub type TfhR = crate::BitReader;
#[doc = "Field `RFH` reader - Receive FIFO is half full"]
pub type RfhR = crate::BitReader;
#[doc = "Field `TFF` reader - Transmit FIFO is full"]
pub type TffR = crate::BitReader;
#[doc = "Field `RFF` reader - Receive FIFO is full"]
pub type RffR = crate::BitReader;
#[doc = "Field `TFE` reader - Transmit FIFO is empty"]
pub type TfeR = crate::BitReader;
#[doc = "Field `RFE` reader - Receive FIFO is empty"]
pub type RfeR = crate::BitReader;
#[doc = "Field `TXDTVAL` reader - Data is valid in transmit FIFO"]
pub type TxdtvalR = crate::BitReader;
#[doc = "Field `RXDTVAL` reader - Data is valid in receive FIFO"]
pub type RxdtvalR = crate::BitReader;
#[doc = "Field `SDIOINT` reader - SD I/O interrupt received"]
pub type SdiointR = crate::BitReader;
#[doc = "Field `ATAEND` reader - CE-ATA command completion signal received"]
pub type AtaendR = crate::BitReader;
impl R {
    #[doc = "Bit 0 - Command response received"]
    #[inline(always)]
    pub fn ccrcerr(&self) -> CcrcerrR {
        CcrcerrR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Data block sent/received"]
    #[inline(always)]
    pub fn dtcrcerr(&self) -> DtcrcerrR {
        DtcrcerrR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Command response timeout"]
    #[inline(always)]
    pub fn cmdtmout(&self) -> CmdtmoutR {
        CmdtmoutR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Data timeout"]
    #[inline(always)]
    pub fn dttmout(&self) -> DttmoutR {
        DttmoutR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Transmit FIFO underrun error occurs"]
    #[inline(always)]
    pub fn txure(&self) -> TxureR {
        TxureR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Received FIFO overrun error occurs"]
    #[inline(always)]
    pub fn rxore(&self) -> RxoreR {
        RxoreR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Command response received"]
    #[inline(always)]
    pub fn cmdrecv(&self) -> CmdrecvR {
        CmdrecvR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Command sent"]
    #[inline(always)]
    pub fn cmdsend(&self) -> CmdsendR {
        CmdsendR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Data end"]
    #[inline(always)]
    pub fn dtend(&self) -> DtendR {
        DtendR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Start bit error in the bus"]
    #[inline(always)]
    pub fn stbite(&self) -> StbiteR {
        StbiteR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Data block sent/received"]
    #[inline(always)]
    pub fn dtblkend(&self) -> DtblkendR {
        DtblkendR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Command transmission in progress"]
    #[inline(always)]
    pub fn cmdrun(&self) -> CmdrunR {
        CmdrunR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Data transmission in progress"]
    #[inline(always)]
    pub fn txrun(&self) -> TxrunR {
        TxrunR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Data reception in progress"]
    #[inline(always)]
    pub fn rxrun(&self) -> RxrunR {
        RxrunR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Transmit FIFO is half empty"]
    #[inline(always)]
    pub fn tfh(&self) -> TfhR {
        TfhR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Receive FIFO is half full"]
    #[inline(always)]
    pub fn rfh(&self) -> RfhR {
        RfhR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - Transmit FIFO is full"]
    #[inline(always)]
    pub fn tff(&self) -> TffR {
        TffR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - Receive FIFO is full"]
    #[inline(always)]
    pub fn rff(&self) -> RffR {
        RffR::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - Transmit FIFO is empty"]
    #[inline(always)]
    pub fn tfe(&self) -> TfeR {
        TfeR::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - Receive FIFO is empty"]
    #[inline(always)]
    pub fn rfe(&self) -> RfeR {
        RfeR::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - Data is valid in transmit FIFO"]
    #[inline(always)]
    pub fn txdtval(&self) -> TxdtvalR {
        TxdtvalR::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - Data is valid in receive FIFO"]
    #[inline(always)]
    pub fn rxdtval(&self) -> RxdtvalR {
        RxdtvalR::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 22 - SD I/O interrupt received"]
    #[inline(always)]
    pub fn sdioint(&self) -> SdiointR {
        SdiointR::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 23 - CE-ATA command completion signal received"]
    #[inline(always)]
    pub fn ataend(&self) -> AtaendR {
        AtaendR::new(((self.bits >> 23) & 1) != 0)
    }
}
#[doc = "Status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`stat::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct StatSpec;
impl crate::RegisterSpec for StatSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`stat::R`](R) reader structure"]
impl crate::Readable for StatSpec {}
#[doc = "`reset()` method sets STAT to value 0"]
impl crate::Resettable for StatSpec {
    const RESET_VALUE: u32 = 0;
}
