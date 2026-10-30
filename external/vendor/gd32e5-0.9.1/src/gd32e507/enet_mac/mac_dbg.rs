#[doc = "Register `MAC_DBG` reader"]
pub type R = crate::R<MacDbgSpec>;
#[doc = "Field `MRNI` reader - MAC receive state not idle"]
pub type MrniR = crate::BitReader;
#[doc = "Field `RXAFS` reader - Rx asynchronous FIFO status"]
pub type RxafsR = crate::FieldReader;
#[doc = "Field `RXFW` reader - RxFIFO is writing"]
pub type RxfwR = crate::BitReader;
#[doc = "Field `RXFRS` reader - RxFIFO read operation status"]
pub type RxfrsR = crate::FieldReader;
#[doc = "Field `RXFS` reader - RxFIFO state"]
pub type RxfsR = crate::FieldReader;
#[doc = "Field `MTNI` reader - MAC transmit state not idle"]
pub type MtniR = crate::BitReader;
#[doc = "Field `SOMT` reader - Status of MAC transmitter"]
pub type SomtR = crate::FieldReader;
#[doc = "Field `PCS` reader - Pause condition status"]
pub type PcsR = crate::BitReader;
#[doc = "Field `TXFRS` reader - TxFIFO read operation status"]
pub type TxfrsR = crate::FieldReader;
#[doc = "Field `TXFW` reader - TxFIFO is writing"]
pub type TxfwR = crate::BitReader;
#[doc = "Field `TXFNE` reader - TxFIFO not empty flag"]
pub type TxfneR = crate::BitReader;
#[doc = "Field `TXFF` reader - TxFIFO Full flag"]
pub type TxffR = crate::BitReader;
impl R {
    #[doc = "Bit 0 - MAC receive state not idle"]
    #[inline(always)]
    pub fn mrni(&self) -> MrniR {
        MrniR::new((self.bits & 1) != 0)
    }
    #[doc = "Bits 1:2 - Rx asynchronous FIFO status"]
    #[inline(always)]
    pub fn rxafs(&self) -> RxafsR {
        RxafsR::new(((self.bits >> 1) & 3) as u8)
    }
    #[doc = "Bit 4 - RxFIFO is writing"]
    #[inline(always)]
    pub fn rxfw(&self) -> RxfwR {
        RxfwR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bits 5:6 - RxFIFO read operation status"]
    #[inline(always)]
    pub fn rxfrs(&self) -> RxfrsR {
        RxfrsR::new(((self.bits >> 5) & 3) as u8)
    }
    #[doc = "Bits 8:9 - RxFIFO state"]
    #[inline(always)]
    pub fn rxfs(&self) -> RxfsR {
        RxfsR::new(((self.bits >> 8) & 3) as u8)
    }
    #[doc = "Bit 16 - MAC transmit state not idle"]
    #[inline(always)]
    pub fn mtni(&self) -> MtniR {
        MtniR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bits 17:18 - Status of MAC transmitter"]
    #[inline(always)]
    pub fn somt(&self) -> SomtR {
        SomtR::new(((self.bits >> 17) & 3) as u8)
    }
    #[doc = "Bit 19 - Pause condition status"]
    #[inline(always)]
    pub fn pcs(&self) -> PcsR {
        PcsR::new(((self.bits >> 19) & 1) != 0)
    }
    #[doc = "Bits 20:21 - TxFIFO read operation status"]
    #[inline(always)]
    pub fn txfrs(&self) -> TxfrsR {
        TxfrsR::new(((self.bits >> 20) & 3) as u8)
    }
    #[doc = "Bit 22 - TxFIFO is writing"]
    #[inline(always)]
    pub fn txfw(&self) -> TxfwR {
        TxfwR::new(((self.bits >> 22) & 1) != 0)
    }
    #[doc = "Bit 24 - TxFIFO not empty flag"]
    #[inline(always)]
    pub fn txfne(&self) -> TxfneR {
        TxfneR::new(((self.bits >> 24) & 1) != 0)
    }
    #[doc = "Bit 25 - TxFIFO Full flag"]
    #[inline(always)]
    pub fn txff(&self) -> TxffR {
        TxffR::new(((self.bits >> 25) & 1) != 0)
    }
}
#[doc = "Ethernet MAC debug register (MAC_DBG)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`mac_dbg::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct MacDbgSpec;
impl crate::RegisterSpec for MacDbgSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`mac_dbg::R`](R) reader structure"]
impl crate::Readable for MacDbgSpec {}
#[doc = "`reset()` method sets MAC_DBG to value 0"]
impl crate::Resettable for MacDbgSpec {
    const RESET_VALUE: u32 = 0;
}
