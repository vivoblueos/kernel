#[doc = "Register `PTP_TSCTL` reader"]
pub type R = crate::R<PtpTsctlSpec>;
#[doc = "Register `PTP_TSCTL` writer"]
pub type W = crate::W<PtpTsctlSpec>;
#[doc = "Field `TMSEN` reader - Time stamp enable"]
pub type TmsenR = crate::BitReader;
#[doc = "Field `TMSEN` writer - Time stamp enable"]
pub type TmsenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TMSFCU` reader - Time stamp fine or coarse update"]
pub type TmsfcuR = crate::BitReader;
#[doc = "Field `TMSFCU` writer - Time stamp fine or coarse update"]
pub type TmsfcuW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TMSSTI` reader - Time stamp system time initialize"]
pub type TmsstiR = crate::BitReader;
#[doc = "Field `TMSSTI` writer - Time stamp system time initialize"]
pub type TmsstiW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TMSSTU` reader - Time stamp system time update"]
pub type TmsstuR = crate::BitReader;
#[doc = "Field `TMSSTU` writer - Time stamp system time update"]
pub type TmsstuW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TMSITEN` reader - Time stamp interrupt trigger enable"]
pub type TmsitenR = crate::BitReader;
#[doc = "Field `TMSITEN` writer - Time stamp interrupt trigger enable"]
pub type TmsitenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TMSARU` reader - Time stamp addend register update"]
pub type TmsaruR = crate::BitReader;
#[doc = "Field `TMSARU` writer - Time stamp addend register update"]
pub type TmsaruW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ARFSEN` reader - All received frames snapshot enable"]
pub type ArfsenR = crate::BitReader;
#[doc = "Field `ARFSEN` writer - All received frames snapshot enable"]
pub type ArfsenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SCROM` reader - Subsecond counter rollover mode"]
pub type ScromR = crate::BitReader;
#[doc = "Field `SCROM` writer - Subsecond counter rollover mode"]
pub type ScromW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PFSV` reader - PTP frame snooping version"]
pub type PfsvR = crate::BitReader;
#[doc = "Field `PFSV` writer - PTP frame snooping version"]
pub type PfsvW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ESEN` reader - Received Ethernet snapshot enable"]
pub type EsenR = crate::BitReader;
#[doc = "Field `ESEN` writer - Received Ethernet snapshot enable"]
pub type EsenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IP6SEN` reader - Received IPv6 snapshot enable"]
pub type Ip6senR = crate::BitReader;
#[doc = "Field `IP6SEN` writer - Received IPv6 snapshot enable"]
pub type Ip6senW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `IP4SEN` reader - Received IPv4 snapshot enable"]
pub type Ip4senR = crate::BitReader;
#[doc = "Field `IP4SEN` writer - Received IPv4 snapshot enable"]
pub type Ip4senW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ETMSEN` reader - Received event type message snapshot enable"]
pub type EtmsenR = crate::BitReader;
#[doc = "Field `ETMSEN` writer - Received event type message snapshot enable"]
pub type EtmsenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `MNMSEN` reader - Received master node message snapshot enable"]
pub type MnmsenR = crate::BitReader;
#[doc = "Field `MNMSEN` writer - Received master node message snapshot enable"]
pub type MnmsenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CKNT` reader - Clock node type for time stamp"]
pub type CkntR = crate::FieldReader;
#[doc = "Field `CKNT` writer - Clock node type for time stamp"]
pub type CkntW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `MAFEN` reader - MAC address filter enable for PTP frame"]
pub type MafenR = crate::BitReader;
#[doc = "Field `MAFEN` writer - MAC address filter enable for PTP frame"]
pub type MafenW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Time stamp enable"]
    #[inline(always)]
    pub fn tmsen(&self) -> TmsenR {
        TmsenR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Time stamp fine or coarse update"]
    #[inline(always)]
    pub fn tmsfcu(&self) -> TmsfcuR {
        TmsfcuR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Time stamp system time initialize"]
    #[inline(always)]
    pub fn tmssti(&self) -> TmsstiR {
        TmsstiR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Time stamp system time update"]
    #[inline(always)]
    pub fn tmsstu(&self) -> TmsstuR {
        TmsstuR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Time stamp interrupt trigger enable"]
    #[inline(always)]
    pub fn tmsiten(&self) -> TmsitenR {
        TmsitenR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - Time stamp addend register update"]
    #[inline(always)]
    pub fn tmsaru(&self) -> TmsaruR {
        TmsaruR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 8 - All received frames snapshot enable"]
    #[inline(always)]
    pub fn arfsen(&self) -> ArfsenR {
        ArfsenR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Subsecond counter rollover mode"]
    #[inline(always)]
    pub fn scrom(&self) -> ScromR {
        ScromR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - PTP frame snooping version"]
    #[inline(always)]
    pub fn pfsv(&self) -> PfsvR {
        PfsvR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Received Ethernet snapshot enable"]
    #[inline(always)]
    pub fn esen(&self) -> EsenR {
        EsenR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Received IPv6 snapshot enable"]
    #[inline(always)]
    pub fn ip6sen(&self) -> Ip6senR {
        Ip6senR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Received IPv4 snapshot enable"]
    #[inline(always)]
    pub fn ip4sen(&self) -> Ip4senR {
        Ip4senR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Received event type message snapshot enable"]
    #[inline(always)]
    pub fn etmsen(&self) -> EtmsenR {
        EtmsenR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Received master node message snapshot enable"]
    #[inline(always)]
    pub fn mnmsen(&self) -> MnmsenR {
        MnmsenR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bits 16:17 - Clock node type for time stamp"]
    #[inline(always)]
    pub fn cknt(&self) -> CkntR {
        CkntR::new(((self.bits >> 16) & 3) as u8)
    }
    #[doc = "Bit 18 - MAC address filter enable for PTP frame"]
    #[inline(always)]
    pub fn mafen(&self) -> MafenR {
        MafenR::new(((self.bits >> 18) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Time stamp enable"]
    #[inline(always)]
    #[must_use]
    pub fn tmsen(&mut self) -> TmsenW<PtpTsctlSpec> {
        TmsenW::new(self, 0)
    }
    #[doc = "Bit 1 - Time stamp fine or coarse update"]
    #[inline(always)]
    #[must_use]
    pub fn tmsfcu(&mut self) -> TmsfcuW<PtpTsctlSpec> {
        TmsfcuW::new(self, 1)
    }
    #[doc = "Bit 2 - Time stamp system time initialize"]
    #[inline(always)]
    #[must_use]
    pub fn tmssti(&mut self) -> TmsstiW<PtpTsctlSpec> {
        TmsstiW::new(self, 2)
    }
    #[doc = "Bit 3 - Time stamp system time update"]
    #[inline(always)]
    #[must_use]
    pub fn tmsstu(&mut self) -> TmsstuW<PtpTsctlSpec> {
        TmsstuW::new(self, 3)
    }
    #[doc = "Bit 4 - Time stamp interrupt trigger enable"]
    #[inline(always)]
    #[must_use]
    pub fn tmsiten(&mut self) -> TmsitenW<PtpTsctlSpec> {
        TmsitenW::new(self, 4)
    }
    #[doc = "Bit 5 - Time stamp addend register update"]
    #[inline(always)]
    #[must_use]
    pub fn tmsaru(&mut self) -> TmsaruW<PtpTsctlSpec> {
        TmsaruW::new(self, 5)
    }
    #[doc = "Bit 8 - All received frames snapshot enable"]
    #[inline(always)]
    #[must_use]
    pub fn arfsen(&mut self) -> ArfsenW<PtpTsctlSpec> {
        ArfsenW::new(self, 8)
    }
    #[doc = "Bit 9 - Subsecond counter rollover mode"]
    #[inline(always)]
    #[must_use]
    pub fn scrom(&mut self) -> ScromW<PtpTsctlSpec> {
        ScromW::new(self, 9)
    }
    #[doc = "Bit 10 - PTP frame snooping version"]
    #[inline(always)]
    #[must_use]
    pub fn pfsv(&mut self) -> PfsvW<PtpTsctlSpec> {
        PfsvW::new(self, 10)
    }
    #[doc = "Bit 11 - Received Ethernet snapshot enable"]
    #[inline(always)]
    #[must_use]
    pub fn esen(&mut self) -> EsenW<PtpTsctlSpec> {
        EsenW::new(self, 11)
    }
    #[doc = "Bit 12 - Received IPv6 snapshot enable"]
    #[inline(always)]
    #[must_use]
    pub fn ip6sen(&mut self) -> Ip6senW<PtpTsctlSpec> {
        Ip6senW::new(self, 12)
    }
    #[doc = "Bit 13 - Received IPv4 snapshot enable"]
    #[inline(always)]
    #[must_use]
    pub fn ip4sen(&mut self) -> Ip4senW<PtpTsctlSpec> {
        Ip4senW::new(self, 13)
    }
    #[doc = "Bit 14 - Received event type message snapshot enable"]
    #[inline(always)]
    #[must_use]
    pub fn etmsen(&mut self) -> EtmsenW<PtpTsctlSpec> {
        EtmsenW::new(self, 14)
    }
    #[doc = "Bit 15 - Received master node message snapshot enable"]
    #[inline(always)]
    #[must_use]
    pub fn mnmsen(&mut self) -> MnmsenW<PtpTsctlSpec> {
        MnmsenW::new(self, 15)
    }
    #[doc = "Bits 16:17 - Clock node type for time stamp"]
    #[inline(always)]
    #[must_use]
    pub fn cknt(&mut self) -> CkntW<PtpTsctlSpec> {
        CkntW::new(self, 16)
    }
    #[doc = "Bit 18 - MAC address filter enable for PTP frame"]
    #[inline(always)]
    #[must_use]
    pub fn mafen(&mut self) -> MafenW<PtpTsctlSpec> {
        MafenW::new(self, 18)
    }
}
#[doc = "Ethernet PTP time stamp control register (PTP_TSCTL)\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ptp_tsctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ptp_tsctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct PtpTsctlSpec;
impl crate::RegisterSpec for PtpTsctlSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`ptp_tsctl::R`](R) reader structure"]
impl crate::Readable for PtpTsctlSpec {}
#[doc = "`write(|w| ..)` method takes [`ptp_tsctl::W`](W) writer structure"]
impl crate::Writable for PtpTsctlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets PTP_TSCTL to value 0"]
impl crate::Resettable for PtpTsctlSpec {
    const RESET_VALUE: u32 = 0;
}
