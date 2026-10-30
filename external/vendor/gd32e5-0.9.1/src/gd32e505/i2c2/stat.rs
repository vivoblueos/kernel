#[doc = "Register `STAT` reader"]
pub type R = crate::R<StatSpec>;
#[doc = "Register `STAT` writer"]
pub type W = crate::W<StatSpec>;
#[doc = "Field `TBE` reader - I2C_TDATA is empty during transmitting"]
pub type TbeR = crate::BitReader;
#[doc = "Field `TBE` writer - I2C_TDATA is empty during transmitting"]
pub type TbeW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TI` reader - Transmit interrupt"]
pub type TiR = crate::BitReader;
#[doc = "Field `TI` writer - Transmit interrupt"]
pub type TiW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RBNE` reader - I2C_RDATA is not empty during receiving"]
pub type RbneR = crate::BitReader;
#[doc = "Field `ADDSEND` reader - Address received matches in slave mode"]
pub type AddsendR = crate::BitReader;
#[doc = "Field `NACK` reader - Not Acknowledge flag"]
pub type NackR = crate::BitReader;
#[doc = "Field `STPDET` reader - STOP condition is detected on the bus"]
pub type StpdetR = crate::BitReader;
#[doc = "Field `TC` reader - Transfer complete in master mode"]
pub type TcR = crate::BitReader;
#[doc = "Field `TCR` reader - Transfer complete reload"]
pub type TcrR = crate::BitReader;
#[doc = "Field `BERR` reader - Bus error"]
pub type BerrR = crate::BitReader;
#[doc = "Field `LOSTARB` reader - Arbitration Lost"]
pub type LostarbR = crate::BitReader;
#[doc = "Field `OUERR` reader - Overrun/Underrun error in slave mode"]
pub type OuerrR = crate::BitReader;
#[doc = "Field `PECERR` reader - PEC error"]
pub type PecerrR = crate::BitReader;
#[doc = "Field `TIMEOUT` reader - TIMEOUT flag"]
pub type TimeoutR = crate::BitReader;
#[doc = "Field `SMBALT` reader - SMBus Alert"]
pub type SmbaltR = crate::BitReader;
#[doc = "Field `I2CBSY` reader - Busy flag"]
pub type I2cbsyR = crate::BitReader;
#[doc = "Field `TR` reader - Whether the I2C is a transmitter or a receiver in slave mode"]
pub type TrR = crate::BitReader;
#[doc = "Field `READDR` reader - Received match address in slave mode"]
pub type ReaddrR = crate::FieldReader;
impl R {
    #[doc = "Bit 0 - I2C_TDATA is empty during transmitting"]
    #[inline(always)]
    pub fn tbe(&self) -> TbeR {
        TbeR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Transmit interrupt"]
    #[inline(always)]
    pub fn ti(&self) -> TiR {
        TiR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - I2C_RDATA is not empty during receiving"]
    #[inline(always)]
    pub fn rbne(&self) -> RbneR {
        RbneR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Address received matches in slave mode"]
    #[inline(always)]
    pub fn addsend(&self) -> AddsendR {
        AddsendR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Not Acknowledge flag"]
    #[inline(always)]
    pub fn nack(&self) -> NackR {
        NackR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - STOP condition is detected on the bus"]
    #[inline(always)]
    pub fn stpdet(&self) -> StpdetR {
        StpdetR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - Transfer complete in master mode"]
    #[inline(always)]
    pub fn tc(&self) -> TcR {
        TcR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Transfer complete reload"]
    #[inline(always)]
    pub fn tcr(&self) -> TcrR {
        TcrR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Bus error"]
    #[inline(always)]
    pub fn berr(&self) -> BerrR {
        BerrR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Arbitration Lost"]
    #[inline(always)]
    pub fn lostarb(&self) -> LostarbR {
        LostarbR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Overrun/Underrun error in slave mode"]
    #[inline(always)]
    pub fn ouerr(&self) -> OuerrR {
        OuerrR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - PEC error"]
    #[inline(always)]
    pub fn pecerr(&self) -> PecerrR {
        PecerrR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - TIMEOUT flag"]
    #[inline(always)]
    pub fn timeout(&self) -> TimeoutR {
        TimeoutR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - SMBus Alert"]
    #[inline(always)]
    pub fn smbalt(&self) -> SmbaltR {
        SmbaltR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 15 - Busy flag"]
    #[inline(always)]
    pub fn i2cbsy(&self) -> I2cbsyR {
        I2cbsyR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bit 16 - Whether the I2C is a transmitter or a receiver in slave mode"]
    #[inline(always)]
    pub fn tr(&self) -> TrR {
        TrR::new(((self.bits >> 16) & 1) != 0)
    }
    #[doc = "Bits 17:23 - Received match address in slave mode"]
    #[inline(always)]
    pub fn readdr(&self) -> ReaddrR {
        ReaddrR::new(((self.bits >> 17) & 0x7f) as u8)
    }
}
impl W {
    #[doc = "Bit 0 - I2C_TDATA is empty during transmitting"]
    #[inline(always)]
    #[must_use]
    pub fn tbe(&mut self) -> TbeW<StatSpec> {
        TbeW::new(self, 0)
    }
    #[doc = "Bit 1 - Transmit interrupt"]
    #[inline(always)]
    #[must_use]
    pub fn ti(&mut self) -> TiW<StatSpec> {
        TiW::new(self, 1)
    }
}
#[doc = "Transfer status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`stat::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`stat::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct StatSpec;
impl crate::RegisterSpec for StatSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`stat::R`](R) reader structure"]
impl crate::Readable for StatSpec {}
#[doc = "`write(|w| ..)` method takes [`stat::W`](W) writer structure"]
impl crate::Writable for StatSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets STAT to value 0x01"]
impl crate::Resettable for StatSpec {
    const RESET_VALUE: u32 = 0x01;
}
