#[doc = "Register `PTP_TSUL` reader"]
pub type R = crate::R<PtpTsulSpec>;
#[doc = "Register `PTP_TSUL` writer"]
pub type W = crate::W<PtpTsulSpec>;
#[doc = "Field `TMSUSS` reader - Time stamp update subseconds"]
pub type TmsussR = crate::FieldReader<u32>;
#[doc = "Field `TMSUSS` writer - Time stamp update subseconds"]
pub type TmsussW<'a, REG> = crate::FieldWriter<'a, REG, 31, u32>;
#[doc = "Field `TMSUPNS` reader - Time stamp update positive or negative sign"]
pub type TmsupnsR = crate::BitReader;
#[doc = "Field `TMSUPNS` writer - Time stamp update positive or negative sign"]
pub type TmsupnsW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:30 - Time stamp update subseconds"]
    #[inline(always)]
    pub fn tmsuss(&self) -> TmsussR {
        TmsussR::new(self.bits & 0x7fff_ffff)
    }
    #[doc = "Bit 31 - Time stamp update positive or negative sign"]
    #[inline(always)]
    pub fn tmsupns(&self) -> TmsupnsR {
        TmsupnsR::new(((self.bits >> 31) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:30 - Time stamp update subseconds"]
    #[inline(always)]
    #[must_use]
    pub fn tmsuss(&mut self) -> TmsussW<PtpTsulSpec> {
        TmsussW::new(self, 0)
    }
    #[doc = "Bit 31 - Time stamp update positive or negative sign"]
    #[inline(always)]
    #[must_use]
    pub fn tmsupns(&mut self) -> TmsupnsW<PtpTsulSpec> {
        TmsupnsW::new(self, 31)
    }
}
#[doc = "Ethernet PTP time stamp low update register (PTP_TSUL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ptp_tsul::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ptp_tsul::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PtpTsulSpec;
impl crate::RegisterSpec for PtpTsulSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ptp_tsul::R`](R) reader structure"]
impl crate::Readable for PtpTsulSpec {}
#[doc = "`write(|w| ..)` method takes [`ptp_tsul::W`](W) writer structure"]
impl crate::Writable for PtpTsulSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets PTP_TSUL to value 0"]
impl crate::Resettable for PtpTsulSpec {
    const RESET_VALUE: u32 = 0;
}
