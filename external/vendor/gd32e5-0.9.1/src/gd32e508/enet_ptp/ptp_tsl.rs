#[doc = "Register `PTP_TSL` reader"]
pub type R = crate::R<PtpTslSpec>;
#[doc = "Field `STMSS` reader - System time subseconds"]
pub type StmssR = crate::FieldReader<u32>;
#[doc = "Field `STS` reader - System time sign"]
pub type StsR = crate::BitReader;
impl R {
    #[doc = "Bits 0:30 - System time subseconds"]
    #[inline(always)]
    pub fn stmss(&self) -> StmssR {
        StmssR::new(self.bits & 0x7fff_ffff)
    }
    #[doc = "Bit 31 - System time sign"]
    #[inline(always)]
    pub fn sts(&self) -> StsR {
        StsR::new(((self.bits >> 31) & 1) != 0)
    }
}
#[doc = "Ethernet PTP time stamp low register (PTP_TSL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ptp_tsl::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PtpTslSpec;
impl crate::RegisterSpec for PtpTslSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ptp_tsl::R`](R) reader structure"]
impl crate::Readable for PtpTslSpec {}
#[doc = "`reset()` method sets PTP_TSL to value 0"]
impl crate::Resettable for PtpTslSpec {
    const RESET_VALUE: u32 = 0;
}
