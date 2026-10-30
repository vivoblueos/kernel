#[doc = "Register `PTP_TSH` reader"]
pub type R = crate::R<PtpTshSpec>;
#[doc = "Field `STMS` reader - System time second"]
pub type StmsR = crate::FieldReader<u32>;
impl R {
    #[doc = "Bits 0:31 - System time second"]
    #[inline(always)]
    pub fn stms(&self) -> StmsR {
        StmsR::new(self.bits)
    }
}
#[doc = "Ethernet PTP time stamp high register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ptp_tsh::R`](R).  See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PtpTshSpec;
impl crate::RegisterSpec for PtpTshSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ptp_tsh::R`](R) reader structure"]
impl crate::Readable for PtpTshSpec {}
#[doc = "`reset()` method sets PTP_TSH to value 0"]
impl crate::Resettable for PtpTshSpec {
    const RESET_VALUE: u32 = 0;
}
