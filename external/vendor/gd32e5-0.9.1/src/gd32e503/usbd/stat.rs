#[doc = "Register `STAT` reader"]
pub type R = crate::R<StatSpec>;
#[doc = "Field `FCNT` reader - Frame number counter"]
pub type FcntR = crate::FieldReader<u16>;
#[doc = "Field `SOFLN` reader - Lost SOF number"]
pub type SoflnR = crate::FieldReader;
#[doc = "Field `LOCK` reader - Locked the USB"]
pub type LockR = crate::BitReader;
#[doc = "Field `RX_DM` reader - Receive data - line status"]
pub type RxDmR = crate::BitReader;
#[doc = "Field `RX_DP` reader - Receive data + line status"]
pub type RxDpR = crate::BitReader;
impl R {
    #[doc = "Bits 0:10 - Frame number counter"]
    #[inline(always)]
    pub fn fcnt(&self) -> FcntR {
        FcntR::new(self.bits & 0x07ff)
    }
    #[doc = "Bits 11:12 - Lost SOF number"]
    #[inline(always)]
    pub fn sofln(&self) -> SoflnR {
        SoflnR::new(((self.bits >> 11) & 3) as u8)
    }
    #[doc = "Bit 13 - Locked the USB"]
    #[inline(always)]
    pub fn lock(&self) -> LockR {
        LockR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Receive data - line status"]
    #[inline(always)]
    pub fn rx_dm(&self) -> RxDmR {
        RxDmR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Receive data + line status"]
    #[inline(always)]
    pub fn rx_dp(&self) -> RxDpR {
        RxDpR::new(((self.bits >> 15) & 1) != 0)
    }
}
#[doc = "Status register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`stat::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct StatSpec;
impl crate::RegisterSpec for StatSpec {
    type Ux = u16;
}
#[doc = "`read()` method returns [`stat::R`](R) reader structure"]
impl crate::Readable for StatSpec {}
#[doc = "`reset()` method sets STAT to value 0"]
impl crate::Resettable for StatSpec {
    const RESET_VALUE: u16 = 0;
}
