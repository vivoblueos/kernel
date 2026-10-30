#[doc = "Register `PTP_TSF` reader"]
pub type R = crate::R<PtpTsfSpec>;
#[doc = "Field `TSSCO` reader - Timestamp second counter overflow"]
pub type TsscoR = crate::BitReader;
#[doc = "Field `TTM` reader - Target time match"]
pub type TtmR = crate::BitReader;
impl R {
    #[doc = "Bit 0 - Timestamp second counter overflow"]
    #[inline(always)]
    pub fn tssco(&self) -> TsscoR {
        TsscoR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Target time match"]
    #[inline(always)]
    pub fn ttm(&self) -> TtmR {
        TtmR::new(((self.bits >> 1) & 1) != 0)
    }
}
#[doc = "Ethernet PTP time stamp flag register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ptp_tsf::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PtpTsfSpec;
impl crate::RegisterSpec for PtpTsfSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ptp_tsf::R`](R) reader structure"]
impl crate::Readable for PtpTsfSpec {}
#[doc = "`reset()` method sets PTP_TSF to value 0"]
impl crate::Resettable for PtpTsfSpec {
    const RESET_VALUE: u32 = 0;
}
