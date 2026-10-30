#[doc = "Register `STATC` writer"]
pub type W = crate::W<StatcSpec>;
#[doc = "Field `ADDSENDC` writer - ADDSEND flag clear"]
pub type AddsendcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `NACKC` writer - Not Acknowledge flag clear"]
pub type NackcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `STPDETC` writer - STPDET flag clear"]
pub type StpdetcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `BERRC` writer - Bus error flag clear"]
pub type BerrcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LOSTARBC` writer - Arbitration Lost flag clear"]
pub type LostarbcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `OUERRC` writer - Overrun/Underrun flag clear"]
pub type OuerrcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PECERRC` writer - PEC error flag clear"]
pub type PecerrcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `TIMEOUTC` writer - TIMEOUT flag clear"]
pub type TimeoutcW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SMBALTC` writer - SMBus Alert flag clear"]
pub type SmbaltcW<'a, REG> = crate::BitWriter<'a, REG>;
impl W {
    #[doc = "Bit 3 - ADDSEND flag clear"]
    #[inline(always)]
    #[must_use]
    pub fn addsendc(&mut self) -> AddsendcW<StatcSpec> {
        AddsendcW::new(self, 3)
    }
    #[doc = "Bit 4 - Not Acknowledge flag clear"]
    #[inline(always)]
    #[must_use]
    pub fn nackc(&mut self) -> NackcW<StatcSpec> {
        NackcW::new(self, 4)
    }
    #[doc = "Bit 5 - STPDET flag clear"]
    #[inline(always)]
    #[must_use]
    pub fn stpdetc(&mut self) -> StpdetcW<StatcSpec> {
        StpdetcW::new(self, 5)
    }
    #[doc = "Bit 8 - Bus error flag clear"]
    #[inline(always)]
    #[must_use]
    pub fn berrc(&mut self) -> BerrcW<StatcSpec> {
        BerrcW::new(self, 8)
    }
    #[doc = "Bit 9 - Arbitration Lost flag clear"]
    #[inline(always)]
    #[must_use]
    pub fn lostarbc(&mut self) -> LostarbcW<StatcSpec> {
        LostarbcW::new(self, 9)
    }
    #[doc = "Bit 10 - Overrun/Underrun flag clear"]
    #[inline(always)]
    #[must_use]
    pub fn ouerrc(&mut self) -> OuerrcW<StatcSpec> {
        OuerrcW::new(self, 10)
    }
    #[doc = "Bit 11 - PEC error flag clear"]
    #[inline(always)]
    #[must_use]
    pub fn pecerrc(&mut self) -> PecerrcW<StatcSpec> {
        PecerrcW::new(self, 11)
    }
    #[doc = "Bit 12 - TIMEOUT flag clear"]
    #[inline(always)]
    #[must_use]
    pub fn timeoutc(&mut self) -> TimeoutcW<StatcSpec> {
        TimeoutcW::new(self, 12)
    }
    #[doc = "Bit 13 - SMBus Alert flag clear"]
    #[inline(always)]
    #[must_use]
    pub fn smbaltc(&mut self) -> SmbaltcW<StatcSpec> {
        SmbaltcW::new(self, 13)
    }
}
#[doc = "Status clear register\n\nYou can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`statc::W`](W). See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct StatcSpec;
impl crate::RegisterSpec for StatcSpec {
    type Ux = u32;
}
#[doc = "`write(|w| ..)` method takes [`statc::W`](W) writer structure"]
impl crate::Writable for StatcSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets STATC to value 0"]
impl crate::Resettable for StatcSpec {
    const RESET_VALUE: u32 = 0;
}
