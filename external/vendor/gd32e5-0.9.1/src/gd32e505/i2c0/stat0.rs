#[doc = "Register `STAT0` reader"]
pub type R = crate::R<Stat0Spec>;
#[doc = "Register `STAT0` writer"]
pub type W = crate::W<Stat0Spec>;
#[doc = "Field `SBSEND` reader - START condition sent out in master mode"]
pub type SbsendR = crate::BitReader;
#[doc = "Field `ADDSEND` reader - Address is sent in master mode or received and matches in slave mode"]
pub type AddsendR = crate::BitReader;
#[doc = "Field `BTC` reader - Byte transmission completed"]
pub type BtcR = crate::BitReader;
#[doc = "Field `ADD10SEND` reader - Header of 10-bit address is sent in master mode"]
pub type Add10sendR = crate::BitReader;
#[doc = "Field `STPDET` reader - STOP condition detected in slave mode"]
pub type StpdetR = crate::BitReader;
#[doc = "Field `RBNE` reader - I2C_DATA is not Empty during receiving"]
pub type RbneR = crate::BitReader;
#[doc = "Field `TBE` reader - I2C_DATA is Empty during transmitting"]
pub type TbeR = crate::BitReader;
#[doc = "Field `BERR` reader - A bus error occurs indication a unexpected START or STOP condition on I2C bus"]
pub type BerrR = crate::BitReader;
#[doc = "Field `BERR` writer - A bus error occurs indication a unexpected START or STOP condition on I2C bus"]
pub type BerrW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LOSTARB` reader - Arbitration Lost in master mode"]
pub type LostarbR = crate::BitReader;
#[doc = "Field `LOSTARB` writer - Arbitration Lost in master mode"]
pub type LostarbW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `AERR` reader - Acknowledge error"]
pub type AerrR = crate::BitReader;
#[doc = "Field `AERR` writer - Acknowledge error"]
pub type AerrW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `OUERR` reader - Over-run or under-run situation occurs in slave mode"]
pub type OuerrR = crate::BitReader;
#[doc = "Field `OUERR` writer - Over-run or under-run situation occurs in slave mode"]
pub type OuerrW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PECERR` reader - PEC error when receiving data"]
pub type PecerrR = crate::BitReader;
#[doc = "Field `PECERR` writer - PEC error when receiving data"]
pub type PecerrW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SMBTO` reader - Timeout signal in SMBus mode"]
pub type SmbtoR = crate::BitReader;
#[doc = "Field `SMBTO` writer - Timeout signal in SMBus mode"]
pub type SmbtoW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SMBALT` reader - SMBus Alert status"]
pub type SmbaltR = crate::BitReader;
#[doc = "Field `SMBALT` writer - SMBus Alert status"]
pub type SmbaltW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - START condition sent out in master mode"]
    #[inline(always)]
    pub fn sbsend(&self) -> SbsendR {
        SbsendR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Address is sent in master mode or received and matches in slave mode"]
    #[inline(always)]
    pub fn addsend(&self) -> AddsendR {
        AddsendR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Byte transmission completed"]
    #[inline(always)]
    pub fn btc(&self) -> BtcR {
        BtcR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Header of 10-bit address is sent in master mode"]
    #[inline(always)]
    pub fn add10send(&self) -> Add10sendR {
        Add10sendR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - STOP condition detected in slave mode"]
    #[inline(always)]
    pub fn stpdet(&self) -> StpdetR {
        StpdetR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 6 - I2C_DATA is not Empty during receiving"]
    #[inline(always)]
    pub fn rbne(&self) -> RbneR {
        RbneR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - I2C_DATA is Empty during transmitting"]
    #[inline(always)]
    pub fn tbe(&self) -> TbeR {
        TbeR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - A bus error occurs indication a unexpected START or STOP condition on I2C bus"]
    #[inline(always)]
    pub fn berr(&self) -> BerrR {
        BerrR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Arbitration Lost in master mode"]
    #[inline(always)]
    pub fn lostarb(&self) -> LostarbR {
        LostarbR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Acknowledge error"]
    #[inline(always)]
    pub fn aerr(&self) -> AerrR {
        AerrR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Over-run or under-run situation occurs in slave mode"]
    #[inline(always)]
    pub fn ouerr(&self) -> OuerrR {
        OuerrR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - PEC error when receiving data"]
    #[inline(always)]
    pub fn pecerr(&self) -> PecerrR {
        PecerrR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 14 - Timeout signal in SMBus mode"]
    #[inline(always)]
    pub fn smbto(&self) -> SmbtoR {
        SmbtoR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - SMBus Alert status"]
    #[inline(always)]
    pub fn smbalt(&self) -> SmbaltR {
        SmbaltR::new(((self.bits >> 15) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 8 - A bus error occurs indication a unexpected START or STOP condition on I2C bus"]
    #[inline(always)]
    #[must_use]
    pub fn berr(&mut self) -> BerrW<Stat0Spec> {
        BerrW::new(self, 8)
    }
    #[doc = "Bit 9 - Arbitration Lost in master mode"]
    #[inline(always)]
    #[must_use]
    pub fn lostarb(&mut self) -> LostarbW<Stat0Spec> {
        LostarbW::new(self, 9)
    }
    #[doc = "Bit 10 - Acknowledge error"]
    #[inline(always)]
    #[must_use]
    pub fn aerr(&mut self) -> AerrW<Stat0Spec> {
        AerrW::new(self, 10)
    }
    #[doc = "Bit 11 - Over-run or under-run situation occurs in slave mode"]
    #[inline(always)]
    #[must_use]
    pub fn ouerr(&mut self) -> OuerrW<Stat0Spec> {
        OuerrW::new(self, 11)
    }
    #[doc = "Bit 12 - PEC error when receiving data"]
    #[inline(always)]
    #[must_use]
    pub fn pecerr(&mut self) -> PecerrW<Stat0Spec> {
        PecerrW::new(self, 12)
    }
    #[doc = "Bit 14 - Timeout signal in SMBus mode"]
    #[inline(always)]
    #[must_use]
    pub fn smbto(&mut self) -> SmbtoW<Stat0Spec> {
        SmbtoW::new(self, 14)
    }
    #[doc = "Bit 15 - SMBus Alert status"]
    #[inline(always)]
    #[must_use]
    pub fn smbalt(&mut self) -> SmbaltW<Stat0Spec> {
        SmbaltW::new(self, 15)
    }
}
#[doc = "Transfer status register 0\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`stat0::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`stat0::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Stat0Spec;
impl crate::RegisterSpec for Stat0Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`stat0::R`](R) reader structure"]
impl crate::Readable for Stat0Spec {}
#[doc = "`write(|w| ..)` method takes [`stat0::W`](W) writer structure"]
impl crate::Writable for Stat0Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets STAT0 to value 0"]
impl crate::Resettable for Stat0Spec {
    const RESET_VALUE: u32 = 0;
}
