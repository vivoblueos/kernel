#[doc = "Register `CTL` reader"]
pub type R = crate::R<CtlSpec>;
#[doc = "Register `CTL` writer"]
pub type W = crate::W<CtlSpec>;
#[doc = "Field `SETRST` reader - Set reset"]
pub type SetrstR = crate::BitReader;
#[doc = "Field `SETRST` writer - Set reset"]
pub type SetrstW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CLOSE` reader - Close state"]
pub type CloseR = crate::BitReader;
#[doc = "Field `CLOSE` writer - Close state"]
pub type CloseW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `LOWM` reader - Low-power mode"]
pub type LowmR = crate::BitReader;
#[doc = "Field `LOWM` writer - Low-power mode"]
pub type LowmW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SETSPS` reader - Set suspend"]
pub type SetspsR = crate::BitReader;
#[doc = "Field `SETSPS` writer - Set suspend"]
pub type SetspsW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RSREQ` reader - Resume request"]
pub type RsreqR = crate::BitReader;
#[doc = "Field `RSREQ` writer - Resume request"]
pub type RsreqW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `L1RSREQ` reader - LPM L1 resume request"]
pub type L1rsreqR = crate::BitReader;
#[doc = "Field `L1RSREQ` writer - LPM L1 resume request"]
pub type L1rsreqW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `L1REQIE` reader - LPM L1 state request interrupt enable"]
pub type L1reqieR = crate::BitReader;
#[doc = "Field `L1REQIE` writer - LPM L1 state request interrupt enable"]
pub type L1reqieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ESOFIE` reader - Expected start of frame interrupt enable"]
pub type EsofieR = crate::BitReader;
#[doc = "Field `ESOFIE` writer - Expected start of frame interrupt enable"]
pub type EsofieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SOFIE` reader - Start of frame interrupt mask"]
pub type SofieR = crate::BitReader;
#[doc = "Field `SOFIE` writer - Start of frame interrupt mask"]
pub type SofieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `RSTIE` reader - USB reset interrupt mask"]
pub type RstieR = crate::BitReader;
#[doc = "Field `RSTIE` writer - USB reset interrupt mask"]
pub type RstieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SPSIE` reader - Suspend mode interrupt mask"]
pub type SpsieR = crate::BitReader;
#[doc = "Field `SPSIE` writer - Suspend mode interrupt mask"]
pub type SpsieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WKUPIE` reader - Wakeup interrupt enable"]
pub type WkupieR = crate::BitReader;
#[doc = "Field `WKUPIE` writer - Wakeup interrupt enable"]
pub type WkupieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ERRIE` reader - Error interrupt mask"]
pub type ErrieR = crate::BitReader;
#[doc = "Field `ERRIE` writer - Error interrupt mask"]
pub type ErrieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `PMOUIE` reader - Packet memory area over / underrun interrupt enable"]
pub type PmouieR = crate::BitReader;
#[doc = "Field `PMOUIE` writer - Packet memory area over / underrun interrupt enable"]
pub type PmouieW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `STIE` reader - Successful transfer interrupt enable"]
pub type StieR = crate::BitReader;
#[doc = "Field `STIE` writer - Successful transfer interrupt enable"]
pub type StieW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - Set reset"]
    #[inline(always)]
    pub fn setrst(&self) -> SetrstR {
        SetrstR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - Close state"]
    #[inline(always)]
    pub fn close(&self) -> CloseR {
        CloseR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bit 2 - Low-power mode"]
    #[inline(always)]
    pub fn lowm(&self) -> LowmR {
        LowmR::new(((self.bits >> 2) & 1) != 0)
    }
    #[doc = "Bit 3 - Set suspend"]
    #[inline(always)]
    pub fn setsps(&self) -> SetspsR {
        SetspsR::new(((self.bits >> 3) & 1) != 0)
    }
    #[doc = "Bit 4 - Resume request"]
    #[inline(always)]
    pub fn rsreq(&self) -> RsreqR {
        RsreqR::new(((self.bits >> 4) & 1) != 0)
    }
    #[doc = "Bit 5 - LPM L1 resume request"]
    #[inline(always)]
    pub fn l1rsreq(&self) -> L1rsreqR {
        L1rsreqR::new(((self.bits >> 5) & 1) != 0)
    }
    #[doc = "Bit 7 - LPM L1 state request interrupt enable"]
    #[inline(always)]
    pub fn l1reqie(&self) -> L1reqieR {
        L1reqieR::new(((self.bits >> 7) & 1) != 0)
    }
    #[doc = "Bit 8 - Expected start of frame interrupt enable"]
    #[inline(always)]
    pub fn esofie(&self) -> EsofieR {
        EsofieR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - Start of frame interrupt mask"]
    #[inline(always)]
    pub fn sofie(&self) -> SofieR {
        SofieR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - USB reset interrupt mask"]
    #[inline(always)]
    pub fn rstie(&self) -> RstieR {
        RstieR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - Suspend mode interrupt mask"]
    #[inline(always)]
    pub fn spsie(&self) -> SpsieR {
        SpsieR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Wakeup interrupt enable"]
    #[inline(always)]
    pub fn wkupie(&self) -> WkupieR {
        WkupieR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - Error interrupt mask"]
    #[inline(always)]
    pub fn errie(&self) -> ErrieR {
        ErrieR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Packet memory area over / underrun interrupt enable"]
    #[inline(always)]
    pub fn pmouie(&self) -> PmouieR {
        PmouieR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Successful transfer interrupt enable"]
    #[inline(always)]
    pub fn stie(&self) -> StieR {
        StieR::new(((self.bits >> 15) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - Set reset"]
    #[inline(always)]
    #[must_use]
    pub fn setrst(&mut self) -> SetrstW<CtlSpec> {
        SetrstW::new(self, 0)
    }
    #[doc = "Bit 1 - Close state"]
    #[inline(always)]
    #[must_use]
    pub fn close(&mut self) -> CloseW<CtlSpec> {
        CloseW::new(self, 1)
    }
    #[doc = "Bit 2 - Low-power mode"]
    #[inline(always)]
    #[must_use]
    pub fn lowm(&mut self) -> LowmW<CtlSpec> {
        LowmW::new(self, 2)
    }
    #[doc = "Bit 3 - Set suspend"]
    #[inline(always)]
    #[must_use]
    pub fn setsps(&mut self) -> SetspsW<CtlSpec> {
        SetspsW::new(self, 3)
    }
    #[doc = "Bit 4 - Resume request"]
    #[inline(always)]
    #[must_use]
    pub fn rsreq(&mut self) -> RsreqW<CtlSpec> {
        RsreqW::new(self, 4)
    }
    #[doc = "Bit 5 - LPM L1 resume request"]
    #[inline(always)]
    #[must_use]
    pub fn l1rsreq(&mut self) -> L1rsreqW<CtlSpec> {
        L1rsreqW::new(self, 5)
    }
    #[doc = "Bit 7 - LPM L1 state request interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn l1reqie(&mut self) -> L1reqieW<CtlSpec> {
        L1reqieW::new(self, 7)
    }
    #[doc = "Bit 8 - Expected start of frame interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn esofie(&mut self) -> EsofieW<CtlSpec> {
        EsofieW::new(self, 8)
    }
    #[doc = "Bit 9 - Start of frame interrupt mask"]
    #[inline(always)]
    #[must_use]
    pub fn sofie(&mut self) -> SofieW<CtlSpec> {
        SofieW::new(self, 9)
    }
    #[doc = "Bit 10 - USB reset interrupt mask"]
    #[inline(always)]
    #[must_use]
    pub fn rstie(&mut self) -> RstieW<CtlSpec> {
        RstieW::new(self, 10)
    }
    #[doc = "Bit 11 - Suspend mode interrupt mask"]
    #[inline(always)]
    #[must_use]
    pub fn spsie(&mut self) -> SpsieW<CtlSpec> {
        SpsieW::new(self, 11)
    }
    #[doc = "Bit 12 - Wakeup interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn wkupie(&mut self) -> WkupieW<CtlSpec> {
        WkupieW::new(self, 12)
    }
    #[doc = "Bit 13 - Error interrupt mask"]
    #[inline(always)]
    #[must_use]
    pub fn errie(&mut self) -> ErrieW<CtlSpec> {
        ErrieW::new(self, 13)
    }
    #[doc = "Bit 14 - Packet memory area over / underrun interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn pmouie(&mut self) -> PmouieW<CtlSpec> {
        PmouieW::new(self, 14)
    }
    #[doc = "Bit 15 - Successful transfer interrupt enable"]
    #[inline(always)]
    #[must_use]
    pub fn stie(&mut self) -> StieW<CtlSpec> {
        StieW::new(self, 15)
    }
}
#[doc = "control register\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`ctl::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`ctl::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct CtlSpec;
impl crate::RegisterSpec for CtlSpec {
    type Ux = u16;
}
#[doc = "`read()` method returns [`ctl::R`](R) reader structure"]
impl crate::Readable for CtlSpec {}
#[doc = "`write(|w| ..)` method takes [`ctl::W`](W) writer structure"]
impl crate::Writable for CtlSpec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u16 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u16 = 0;
}
#[doc = "`reset()` method sets CTL to value 0x03"]
impl crate::Resettable for CtlSpec {
    const RESET_VALUE: u16 = 0x03;
}
