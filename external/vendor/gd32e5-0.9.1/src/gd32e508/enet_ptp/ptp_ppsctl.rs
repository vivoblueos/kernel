#[doc = "Register `PTP_PPSCTL` reader"]
pub type R = crate::R<PtpPpsctlSpec>;
#[doc = "Register `PTP_PPSCTL` writer"]
pub type W = crate::W<PtpPpsctlSpec>;
#[doc = "Field `PPSOFC` reader - PPS output frequency configure"]
pub type PpsofcR = crate::FieldReader;
#[doc = "Field `PPSOFC` writer - PPS output frequency configure"]
pub type PpsofcW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
impl R {
    #[doc = "Bits 0:3 - PPS output frequency configure"]
    #[inline(always)]
    pub fn ppsofc(&self) -> PpsofcR {
        PpsofcR::new((self.bits & 0x0f) as u8)
    }
}
impl W {
    #[doc = "Bits 0:3 - PPS output frequency configure"]
    #[inline(always)]
    #[must_use]
    pub fn ppsofc(&mut self) -> PpsofcW<PtpPpsctlSpec> {
        PpsofcW::new(self, 0)
    }
}
#[doc = "Ethernet PTP PPS control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ptp_ppsctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ptp_ppsctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PtpPpsctlSpec;
impl crate::RegisterSpec for PtpPpsctlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ptp_ppsctl::R`](R) reader structure"]
impl crate::Readable for PtpPpsctlSpec {}
#[doc = "`write(|w| ..)` method takes [`ptp_ppsctl::W`](W) writer structure"]
impl crate::Writable for PtpPpsctlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets PTP_PPSCTL to value 0"]
impl crate::Resettable for PtpPpsctlSpec {
    const RESET_VALUE: u32 = 0;
}
