#[doc = "Register `STAT1` reader"]
pub type R = crate::R<Stat1Spec>;
#[doc = "Field `MASTER` reader - A flag indicating whether I2C block is in master or slave mode"]
pub type MasterR = crate::BitReader;
#[doc = "Field `I2CBSY` reader - Busy flag"]
pub type I2cbsyR = crate::BitReader;
#[doc = "Field `TR` reader - Whether the I2C is a transmitter or a receiver"]
pub type TrR = crate::BitReader;
#[doc = "Field `RXGC` reader - General call address (00h) received"]
pub type RxgcR = crate::BitReader;
#[doc = "Field `DEFSMB` reader - Default address of SMBusDevice"]
pub type DefsmbR = crate::BitReader;
#[doc = "Field `HSTSMB` reader - SMBus Host Header detected in slave mode"]
pub type HstsmbR = crate::BitReader;
#[doc = "Field `DUMODF` reader - Dual Flag in slave mode"]
pub type DumodfR = crate::BitReader;
#[doc = "Field `PECV` reader - Packet Error Checking Value that calculated by hardware when PEC is enabled"]
pub type PecvR = crate::FieldReader;
impl R {
    #[doc = "Bit 0 - A flag indicating whether I2C block is in master or slave mode"]
    #[inline(always)]
    pub fn master(&self) -> MasterR {
        MasterR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Busy flag"]
    #[inline(always)]
    pub fn i2cbsy(&self) -> I2cbsyR {
        I2cbsyR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Whether the I2C is a transmitter or a receiver"]
    #[inline(always)]
    pub fn tr(&self) -> TrR {
        TrR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 4 - General call address (00h) received"]
    #[inline(always)]
    pub fn rxgc(&self) -> RxgcR {
        RxgcR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Default address of SMBusDevice"]
    #[inline(always)]
    pub fn defsmb(&self) -> DefsmbR {
        DefsmbR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 6 - SMBus Host Header detected in slave mode"]
    #[inline(always)]
    pub fn hstsmb(&self) -> HstsmbR {
        HstsmbR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 7 - Dual Flag in slave mode"]
    #[inline(always)]
    pub fn dumodf(&self) -> DumodfR {
        DumodfR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bits 8:15 - Packet Error Checking Value that calculated by hardware when PEC is enabled"]
    #[inline(always)]
    pub fn pecv(&self) -> PecvR {
        PecvR::new(((self.bits >> 8) & 0xff) as u8)
    }
}
#[doc = "Transfer status register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`stat1::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Stat1Spec;
impl crate::RegisterSpec for Stat1Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`stat1::R`](R) reader structure"]
impl crate::Readable for Stat1Spec {}
#[doc = "`reset()` method sets STAT1 to value 0"]
impl crate::Resettable for Stat1Spec {
    const RESET_VALUE: u32 = 0;
}
