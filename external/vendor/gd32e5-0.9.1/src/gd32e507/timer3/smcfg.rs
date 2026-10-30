#[doc = "Register `SMCFG` reader"]
pub type R = crate::R<SmcfgSpec>;
#[doc = "Register `SMCFG` writer"]
pub type W = crate::W<SmcfgSpec>;
#[doc = "Field `SMC` reader - Slave mode control"]
pub type SmcR = crate::FieldReader;
#[doc = "Field `SMC` writer - Slave mode control"]
pub type SmcW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `TRGS` reader - Trigger selection"]
pub type TrgsR = crate::FieldReader;
#[doc = "Field `TRGS` writer - Trigger selection"]
pub type TrgsW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `MSM` reader - Master-slave mode"]
pub type MsmR = crate::BitReader;
#[doc = "Field `MSM` writer - Master-slave mode"]
pub type MsmW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ETFC` reader - External trigger filter control"]
pub type EtfcR = crate::FieldReader;
#[doc = "Field `ETFC` writer - External trigger filter control"]
pub type EtfcW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `ETPSC` reader - External trigger prescaler"]
pub type EtpscR = crate::FieldReader;
#[doc = "Field `ETPSC` writer - External trigger prescaler"]
pub type EtpscW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `SMC1` reader - Part of SMC for enable External clock mode1"]
pub type Smc1R = crate::BitReader;
#[doc = "Field `SMC1` writer - Part of SMC for enable External clock mode1"]
pub type Smc1W<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ETP` reader - External trigger polarity"]
pub type EtpR = crate::BitReader;
#[doc = "Field `ETP` writer - External trigger polarity"]
pub type EtpW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:2 - Slave mode control"]
    #[inline(always)]
    pub fn smc(&self) -> SmcR {
        SmcR::new((self.bits & 7) as u8)
    }
    #[doc = "Bits 4:6 - Trigger selection"]
    #[inline(always)]
    pub fn trgs(&self) -> TrgsR {
        TrgsR::new(((self.bits >> 4) & 7) as u8)
    }
    #[doc = "Bit 7 - Master-slave mode"]
    #[inline(always)]
    pub fn msm(&self) -> MsmR {
        MsmR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bits 8:11 - External trigger filter control"]
    #[inline(always)]
    pub fn etfc(&self) -> EtfcR {
        EtfcR::new(((self.bits >> 8) & 0x0f) as u8)
    }
    #[doc = "Bits 12:13 - External trigger prescaler"]
    #[inline(always)]
    pub fn etpsc(&self) -> EtpscR {
        EtpscR::new(((self.bits >> 12) & 3) as u8)
    }
    #[doc = "Bit 14 - Part of SMC for enable External clock mode1"]
    #[inline(always)]
    pub fn smc1(&self) -> Smc1R {
        Smc1R::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - External trigger polarity"]
    #[inline(always)]
    pub fn etp(&self) -> EtpR {
        EtpR::new(((self.bits >> 15) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:2 - Slave mode control"]
    #[inline(always)]
    #[must_use]
    pub fn smc(&mut self) -> SmcW<SmcfgSpec> {
        SmcW::new(self, 0)
    }
    #[doc = "Bits 4:6 - Trigger selection"]
    #[inline(always)]
    #[must_use]
    pub fn trgs(&mut self) -> TrgsW<SmcfgSpec> {
        TrgsW::new(self, 4)
    }
    #[doc = "Bit 7 - Master-slave mode"]
    #[inline(always)]
    #[must_use]
    pub fn msm(&mut self) -> MsmW<SmcfgSpec> {
        MsmW::new(self, 7)
    }
    #[doc = "Bits 8:11 - External trigger filter control"]
    #[inline(always)]
    #[must_use]
    pub fn etfc(&mut self) -> EtfcW<SmcfgSpec> {
        EtfcW::new(self, 8)
    }
    #[doc = "Bits 12:13 - External trigger prescaler"]
    #[inline(always)]
    #[must_use]
    pub fn etpsc(&mut self) -> EtpscW<SmcfgSpec> {
        EtpscW::new(self, 12)
    }
    #[doc = "Bit 14 - Part of SMC for enable External clock mode1"]
    #[inline(always)]
    #[must_use]
    pub fn smc1(&mut self) -> Smc1W<SmcfgSpec> {
        Smc1W::new(self, 14)
    }
    #[doc = "Bit 15 - External trigger polarity"]
    #[inline(always)]
    #[must_use]
    pub fn etp(&mut self) -> EtpW<SmcfgSpec> {
        EtpW::new(self, 15)
    }
}
#[doc = "slave mode control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`smcfg::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`smcfg::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct SmcfgSpec;
impl crate::RegisterSpec for SmcfgSpec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`smcfg::R`](R) reader structure"]
impl crate::Readable for SmcfgSpec {}
#[doc = "`write(|w| ..)` method takes [`smcfg::W`](W) writer structure"]
impl crate::Writable for SmcfgSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets SMCFG to value 0"]
impl crate::Resettable for SmcfgSpec {
    const RESET_VALUE: u32 = 0;
}
