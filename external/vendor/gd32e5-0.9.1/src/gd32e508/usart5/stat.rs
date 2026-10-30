#[doc = "Register `STAT` reader"]
pub type R = crate::R<StatSpec>;
#[doc = "Field `PERR` reader - Parity error flag"]
pub type PerrR = crate::BitReader;
#[doc = "Field `FERR` reader - Frame error flag"]
pub type FerrR = crate::BitReader;
#[doc = "Field `NERR` reader - Noise error flag"]
pub type NerrR = crate::BitReader;
#[doc = "Field `ORERR` reader - Overrun error"]
pub type OrerrR = crate::BitReader;
#[doc = "Field `IDLEF` reader - IDLE line detected flag"]
pub type IdlefR = crate::BitReader;
#[doc = "Field `RBNE` reader - Read data buffer not empty"]
pub type RbneR = crate::BitReader;
#[doc = "Field `TC` reader - Transmission completed"]
pub type TcR = crate::BitReader;
#[doc = "Field `TBE` reader - Transmit data register empty"]
pub type TbeR = crate::BitReader;
#[doc = "Field `LBDF` reader - LIN break detected flag"]
pub type LbdfR = crate::BitReader;
#[doc = "Field `RTF` reader - Receiver timeout flag"]
pub type RtfR = crate::BitReader;
#[doc = "Field `EBF` reader - End of block flag"]
pub type EbfR = crate::BitReader;
#[doc = "Field `ABDE` reader - Auto baudrate detection error"]
pub type AbdeR = crate::BitReader;
#[doc = "Field `ABDF` reader - Auto baudrate detection flag"]
pub type AbdfR = crate::BitReader;
#[doc = "Field `BSY` reader - Busy flag"]
pub type BsyR = crate::BitReader;
#[doc = "Field `AMF` reader - ADDR match flag"]
pub type AmfR = crate::BitReader;
#[doc = "Field `SBF` reader - Send break flag"]
pub type SbfR = crate::BitReader;
#[doc = "Field `RWU` reader - Receiver wakeup from mute mode"]
pub type RwuR = crate::BitReader;
#[doc = "Field `WUF` reader - Wakeup from Deep-sleep mode flag"]
pub type WufR = crate::BitReader;
#[doc = "Field `TEA` reader - Transmit enable acknowledge flag"]
pub type TeaR = crate::BitReader;
#[doc = "Field `REA` reader - Receive enable acknowledge flag"]
pub type ReaR = crate::BitReader;
impl R {
    #[doc = "Bit 0 - Parity error flag"]
    #[inline(always)]
    pub fn perr(&self) -> PerrR {
        PerrR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Frame error flag"]
    #[inline(always)]
    pub fn ferr(&self) -> FerrR {
        FerrR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Noise error flag"]
    #[inline(always)]
    pub fn nerr(&self) -> NerrR {
        NerrR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Overrun error"]
    #[inline(always)]
    pub fn orerr(&self) -> OrerrR {
        OrerrR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - IDLE line detected flag"]
    #[inline(always)]
    pub fn idlef(&self) -> IdlefR {
        IdlefR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Read data buffer not empty"]
    #[inline(always)]
    pub fn rbne(&self) -> RbneR {
        RbneR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Transmission completed"]
    #[inline(always)]
    pub fn tc(&self) -> TcR {
        TcR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Transmit data register empty"]
    #[inline(always)]
    pub fn tbe(&self) -> TbeR {
        TbeR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - LIN break detected flag"]
    #[inline(always)]
    pub fn lbdf(&self) -> LbdfR {
        LbdfR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 11 - Receiver timeout flag"]
    #[inline(always)]
    pub fn rtf(&self) -> RtfR {
        RtfR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - End of block flag"]
    #[inline(always)]
    pub fn ebf(&self) -> EbfR {
        EbfR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 14 - Auto baudrate detection error"]
    #[inline(always)]
    pub fn abde(&self) -> AbdeR {
        AbdeR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Auto baudrate detection flag"]
    #[inline(always)]
    pub fn abdf(&self) -> AbdfR {
        AbdfR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - Busy flag"]
    #[inline(always)]
    pub fn bsy(&self) -> BsyR {
        BsyR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bit 17 - ADDR match flag"]
    #[inline(always)]
    pub fn amf(&self) -> AmfR {
        AmfR::new(((self.bits >> 17) & 1) != 0)
    }
    #[doc = "Bit 18 - Send break flag"]
    #[inline(always)]
    pub fn sbf(&self) -> SbfR {
        SbfR::new(((self.bits >> 18) & 1) != 0)
    }
    #[doc = "Bit 19 - Receiver wakeup from mute mode"]
    #[inline(always)]
    pub fn rwu(&self) -> RwuR {
        RwuR::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bit 20 - Wakeup from Deep-sleep mode flag"]
    #[inline(always)]
    pub fn wuf(&self) -> WufR {
        WufR::new(((self.bits >> 20) & 1) != 0)
    }
    #[doc = "Bit 21 - Transmit enable acknowledge flag"]
    #[inline(always)]
    pub fn tea(&self) -> TeaR {
        TeaR::new(((self.bits >> 21) & 1) != 0)
    }
    #[doc = "Bit 22 - Receive enable acknowledge flag"]
    #[inline(always)]
    pub fn rea(&self) -> ReaR {
        ReaR::new(((self.bits >> 22) & 1) != 0)
    }
}
#[doc = "Status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`stat::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct StatSpec;
impl crate::RegisterSpec for StatSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`stat::R`](R) reader structure"]
impl crate::Readable for StatSpec {}
#[doc = "`reset()` method sets STAT to value 0xc0"]
impl crate::Resettable for StatSpec {
    const RESET_VALUE: u32 = 0xc0;
}
