#[doc = "Register `INTF` reader"]
pub type R = crate::R<IntfSpec>;
#[doc = "Register `INTF` writer"]
pub type W = crate::W<IntfSpec>;
#[doc = "Field `EPNUM` reader - Endpoint Identifier"]
pub type EpnumR = crate::FieldReader;
#[doc = "Field `EPNUM` writer - Endpoint Identifier"]
pub type EpnumW<'a, REG> = crate::FieldWriter<'a, REG, 4>;
#[doc = "Field `DIR` reader - Direction of transaction"]
pub type DirR = crate::BitReader;
#[doc = "Field `DIR` writer - Direction of transaction"]
pub type DirW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `L1REQ` reader - LPM L1 transaction is successful"]
pub type L1reqR = crate::BitReader;
#[doc = "Field `L1REQ` writer - LPM L1 transaction is successful"]
pub type L1reqW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ESOFIF` reader - Expected start of frame interrupt flag"]
pub type EsofifR = crate::BitReader;
#[doc = "Field `ESOFIF` writer - Expected start of frame interrupt flag"]
pub type EsofifW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SOFIF` reader - start of frame interrupt flag"]
pub type SofifR = crate::BitReader;
#[doc = "Field `SOFIF` writer - start of frame interrupt flag"]
pub type SofifW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RSTIF` reader - reset interrupt flag"]
pub type RstifR = crate::BitReader;
#[doc = "Field `RSTIF` writer - reset interrupt flag"]
pub type RstifW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPSIF` reader - Suspend mode interrupt flag"]
pub type SpsifR = crate::BitReader;
#[doc = "Field `SPSIF` writer - Suspend mode interrupt flag"]
pub type SpsifW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WKUPIF` reader - Wakeup interrupt flag"]
pub type WkupifR = crate::BitReader;
#[doc = "Field `WKUPIF` writer - Wakeup interrupt flag"]
pub type WkupifW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ERRIF` reader - Error interrupt flag"]
pub type ErrifR = crate::BitReader;
#[doc = "Field `ERRIF` writer - Error interrupt flag"]
pub type ErrifW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PMOUIF` reader - Packet memory area over / underrun interrupt flag"]
pub type PmouifR = crate::BitReader;
#[doc = "Field `PMOUIF` writer - Packet memory area over / underrun interrupt flag"]
pub type PmouifW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `STIF` reader - Successful transfer interrupt flag"]
pub type StifR = crate::BitReader;
#[doc = "Field `STIF` writer - Successful transfer interrupt flag"]
pub type StifW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bits 0:3 - Endpoint Identifier"]
    #[inline(always)]
    pub fn epnum(&self) -> EpnumR {
        EpnumR::new((self.bits & 0x0f) as u8)
    }
    #[doc = "Bit 4 - Direction of transaction"]
    #[inline(always)]
    pub fn dir(&self) -> DirR {
        DirR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 7 - LPM L1 transaction is successful"]
    #[inline(always)]
    pub fn l1req(&self) -> L1reqR {
        L1reqR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Expected start of frame interrupt flag"]
    #[inline(always)]
    pub fn esofif(&self) -> EsofifR {
        EsofifR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - start of frame interrupt flag"]
    #[inline(always)]
    pub fn sofif(&self) -> SofifR {
        SofifR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - reset interrupt flag"]
    #[inline(always)]
    pub fn rstif(&self) -> RstifR {
        RstifR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Suspend mode interrupt flag"]
    #[inline(always)]
    pub fn spsif(&self) -> SpsifR {
        SpsifR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Wakeup interrupt flag"]
    #[inline(always)]
    pub fn wkupif(&self) -> WkupifR {
        WkupifR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Error interrupt flag"]
    #[inline(always)]
    pub fn errif(&self) -> ErrifR {
        ErrifR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Packet memory area over / underrun interrupt flag"]
    #[inline(always)]
    pub fn pmouif(&self) -> PmouifR {
        PmouifR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Successful transfer interrupt flag"]
    #[inline(always)]
    pub fn stif(&self) -> StifR {
        StifR::new(((self.bits >> 15) & 1) != 0)
    }
}
impl W {
    #[doc = "Bits 0:3 - Endpoint Identifier"]
    #[inline(always)]
    #[must_use]
    pub fn epnum(&mut self) -> EpnumW<IntfSpec> {
        EpnumW::new(self, 0)
    }
    #[doc = "Bit 4 - Direction of transaction"]
    #[inline(always)]
    #[must_use]
    pub fn dir(&mut self) -> DirW<IntfSpec> {
        DirW::new(self, 4)
    }
    #[doc = "Bit 7 - LPM L1 transaction is successful"]
    #[inline(always)]
    #[must_use]
    pub fn l1req(&mut self) -> L1reqW<IntfSpec> {
        L1reqW::new(self, 7)
    }
    #[doc = "Bit 8 - Expected start of frame interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn esofif(&mut self) -> EsofifW<IntfSpec> {
        EsofifW::new(self, 8)
    }
    #[doc = "Bit 9 - start of frame interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn sofif(&mut self) -> SofifW<IntfSpec> {
        SofifW::new(self, 9)
    }
    #[doc = "Bit 10 - reset interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn rstif(&mut self) -> RstifW<IntfSpec> {
        RstifW::new(self, 10)
    }
    #[doc = "Bit 11 - Suspend mode interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn spsif(&mut self) -> SpsifW<IntfSpec> {
        SpsifW::new(self, 11)
    }
    #[doc = "Bit 12 - Wakeup interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn wkupif(&mut self) -> WkupifW<IntfSpec> {
        WkupifW::new(self, 12)
    }
    #[doc = "Bit 13 - Error interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn errif(&mut self) -> ErrifW<IntfSpec> {
        ErrifW::new(self, 13)
    }
    #[doc = "Bit 14 - Packet memory area over / underrun interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn pmouif(&mut self) -> PmouifW<IntfSpec> {
        PmouifW::new(self, 14)
    }
    #[doc = "Bit 15 - Successful transfer interrupt flag"]
    #[inline(always)]
    #[must_use]
    pub fn stif(&mut self) -> StifW<IntfSpec> {
        StifW::new(self, 15)
    }
}
#[doc = "interrupt flag register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`intf::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`intf::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct IntfSpec;
impl crate::RegisterSpec for IntfSpec {
    type Ux = u16;
}
#[doc = "`read()` method returns [`intf::R`](R) reader structure"]
impl crate::Readable for IntfSpec {}
#[doc = "`write(|w| ..)` method takes [`intf::W`](W) writer structure"]
impl crate::Writable for IntfSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u16 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u16 = 0;
}
#[doc = "`reset()` method sets INTF to value 0"]
impl crate::Resettable for IntfSpec {
    const RESET_VALUE: u16 = 0;
}
