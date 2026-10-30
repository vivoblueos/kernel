#[doc = "Register `SNCTL1` reader"]
pub type R = crate::R<Snctl1Spec>;
#[doc = "Register `SNCTL1` writer"]
pub type W = crate::W<Snctl1Spec>;
#[doc = "Field `NRBKEN` reader - NOR bank enable"]
pub type NrbkenR = crate::BitReader;
#[doc = "Field `NRBKEN` writer - NOR bank enable"]
pub type NrbkenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `NRMUX` reader - NOR bank memory address/data multiplexing"]
pub type NrmuxR = crate::BitReader;
#[doc = "Field `NRMUX` writer - NOR bank memory address/data multiplexing"]
pub type NrmuxW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `NRTP` reader - NOR bank memory type"]
pub type NrtpR = crate::FieldReader;
#[doc = "Field `NRTP` writer - NOR bank memory type"]
pub type NrtpW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `NRW` reader - NOR bank memory data bus width"]
pub type NrwR = crate::FieldReader;
#[doc = "Field `NRW` writer - NOR bank memory data bus width"]
pub type NrwW<'a, REG> = crate::FieldWriter<'a, REG, 2>;
#[doc = "Field `NREN` reader - NOR Flash access enable"]
pub type NrenR = crate::BitReader;
#[doc = "Field `NREN` writer - NOR Flash access enable"]
pub type NrenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `SBRSTEN` reader - Synchronous burst enable"]
pub type SbrstenR = crate::BitReader;
#[doc = "Field `SBRSTEN` writer - Synchronous burst enable"]
pub type SbrstenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `NRWTPOL` reader - NWAIT signal polarity"]
pub type NrwtpolR = crate::BitReader;
#[doc = "Field `NRWTPOL` writer - NWAIT signal polarity"]
pub type NrwtpolW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WRAPEN` reader - Wrapped burst mode enable"]
pub type WrapenR = crate::BitReader;
#[doc = "Field `WRAPEN` writer - Wrapped burst mode enable"]
pub type WrapenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `NRWTCFG` reader - NWAIT signal configuration, only work in synchronous mode"]
pub type NrwtcfgR = crate::BitReader;
#[doc = "Field `NRWTCFG` writer - NWAIT signal configuration, only work in synchronous mode"]
pub type NrwtcfgW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `WREN` reader - Write enable"]
pub type WrenR = crate::BitReader;
#[doc = "Field `WREN` writer - Write enable"]
pub type WrenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `NRWTEN` reader - NWAIT signal enable"]
pub type NrwtenR = crate::BitReader;
#[doc = "Field `NRWTEN` writer - NWAIT signal enable"]
pub type NrwtenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `EXMODEN` reader - Extended mode enable"]
pub type ExmodenR = crate::BitReader;
#[doc = "Field `EXMODEN` writer - Extended mode enable"]
pub type ExmodenW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `ASYNCWAIT` reader - Asynchronous wait"]
pub type AsyncwaitR = crate::BitReader;
#[doc = "Field `ASYNCWAIT` writer - Asynchronous wait"]
pub type AsyncwaitW<'a, REG> = crate::BitWriter<'a, REG>;
#[doc = "Field `CPS` reader - CRAM page size"]
pub type CpsR = crate::FieldReader;
#[doc = "Field `CPS` writer - CRAM page size"]
pub type CpsW<'a, REG> = crate::FieldWriter<'a, REG, 3>;
#[doc = "Field `SYNCWR` reader - Synchronous write"]
pub type SyncwrR = crate::BitReader;
#[doc = "Field `SYNCWR` writer - Synchronous write"]
pub type SyncwrW<'a, REG> = crate::BitWriter<'a, REG>;
impl R {
    #[doc = "Bit 0 - NOR bank enable"]
    #[inline(always)]
    pub fn nrbken(&self) -> NrbkenR {
        NrbkenR::new((self.bits & 1) != 0)
    }
    #[doc = "Bit 1 - NOR bank memory address/data multiplexing"]
    #[inline(always)]
    pub fn nrmux(&self) -> NrmuxR {
        NrmuxR::new(((self.bits >> 1) & 1) != 0)
    }
    #[doc = "Bits 2:3 - NOR bank memory type"]
    #[inline(always)]
    pub fn nrtp(&self) -> NrtpR {
        NrtpR::new(((self.bits >> 2) & 3) as u8)
    }
    #[doc = "Bits 4:5 - NOR bank memory data bus width"]
    #[inline(always)]
    pub fn nrw(&self) -> NrwR {
        NrwR::new(((self.bits >> 4) & 3) as u8)
    }
    #[doc = "Bit 6 - NOR Flash access enable"]
    #[inline(always)]
    pub fn nren(&self) -> NrenR {
        NrenR::new(((self.bits >> 6) & 1) != 0)
    }
    #[doc = "Bit 8 - Synchronous burst enable"]
    #[inline(always)]
    pub fn sbrsten(&self) -> SbrstenR {
        SbrstenR::new(((self.bits >> 8) & 1) != 0)
    }
    #[doc = "Bit 9 - NWAIT signal polarity"]
    #[inline(always)]
    pub fn nrwtpol(&self) -> NrwtpolR {
        NrwtpolR::new(((self.bits >> 9) & 1) != 0)
    }
    #[doc = "Bit 10 - Wrapped burst mode enable"]
    #[inline(always)]
    pub fn wrapen(&self) -> WrapenR {
        WrapenR::new(((self.bits >> 10) & 1) != 0)
    }
    #[doc = "Bit 11 - NWAIT signal configuration, only work in synchronous mode"]
    #[inline(always)]
    pub fn nrwtcfg(&self) -> NrwtcfgR {
        NrwtcfgR::new(((self.bits >> 11) & 1) != 0)
    }
    #[doc = "Bit 12 - Write enable"]
    #[inline(always)]
    pub fn wren(&self) -> WrenR {
        WrenR::new(((self.bits >> 12) & 1) != 0)
    }
    #[doc = "Bit 13 - NWAIT signal enable"]
    #[inline(always)]
    pub fn nrwten(&self) -> NrwtenR {
        NrwtenR::new(((self.bits >> 13) & 1) != 0)
    }
    #[doc = "Bit 14 - Extended mode enable"]
    #[inline(always)]
    pub fn exmoden(&self) -> ExmodenR {
        ExmodenR::new(((self.bits >> 14) & 1) != 0)
    }
    #[doc = "Bit 15 - Asynchronous wait"]
    #[inline(always)]
    pub fn asyncwait(&self) -> AsyncwaitR {
        AsyncwaitR::new(((self.bits >> 15) & 1) != 0)
    }
    #[doc = "Bits 16:18 - CRAM page size"]
    #[inline(always)]
    pub fn cps(&self) -> CpsR {
        CpsR::new(((self.bits >> 16) & 7) as u8)
    }
    #[doc = "Bit 19 - Synchronous write"]
    #[inline(always)]
    pub fn syncwr(&self) -> SyncwrR {
        SyncwrR::new(((self.bits >> 19) & 1) != 0)
    }
}
impl W {
    #[doc = "Bit 0 - NOR bank enable"]
    #[inline(always)]
    #[must_use]
    pub fn nrbken(&mut self) -> NrbkenW<Snctl1Spec> {
        NrbkenW::new(self, 0)
    }
    #[doc = "Bit 1 - NOR bank memory address/data multiplexing"]
    #[inline(always)]
    #[must_use]
    pub fn nrmux(&mut self) -> NrmuxW<Snctl1Spec> {
        NrmuxW::new(self, 1)
    }
    #[doc = "Bits 2:3 - NOR bank memory type"]
    #[inline(always)]
    #[must_use]
    pub fn nrtp(&mut self) -> NrtpW<Snctl1Spec> {
        NrtpW::new(self, 2)
    }
    #[doc = "Bits 4:5 - NOR bank memory data bus width"]
    #[inline(always)]
    #[must_use]
    pub fn nrw(&mut self) -> NrwW<Snctl1Spec> {
        NrwW::new(self, 4)
    }
    #[doc = "Bit 6 - NOR Flash access enable"]
    #[inline(always)]
    #[must_use]
    pub fn nren(&mut self) -> NrenW<Snctl1Spec> {
        NrenW::new(self, 6)
    }
    #[doc = "Bit 8 - Synchronous burst enable"]
    #[inline(always)]
    #[must_use]
    pub fn sbrsten(&mut self) -> SbrstenW<Snctl1Spec> {
        SbrstenW::new(self, 8)
    }
    #[doc = "Bit 9 - NWAIT signal polarity"]
    #[inline(always)]
    #[must_use]
    pub fn nrwtpol(&mut self) -> NrwtpolW<Snctl1Spec> {
        NrwtpolW::new(self, 9)
    }
    #[doc = "Bit 10 - Wrapped burst mode enable"]
    #[inline(always)]
    #[must_use]
    pub fn wrapen(&mut self) -> WrapenW<Snctl1Spec> {
        WrapenW::new(self, 10)
    }
    #[doc = "Bit 11 - NWAIT signal configuration, only work in synchronous mode"]
    #[inline(always)]
    #[must_use]
    pub fn nrwtcfg(&mut self) -> NrwtcfgW<Snctl1Spec> {
        NrwtcfgW::new(self, 11)
    }
    #[doc = "Bit 12 - Write enable"]
    #[inline(always)]
    #[must_use]
    pub fn wren(&mut self) -> WrenW<Snctl1Spec> {
        WrenW::new(self, 12)
    }
    #[doc = "Bit 13 - NWAIT signal enable"]
    #[inline(always)]
    #[must_use]
    pub fn nrwten(&mut self) -> NrwtenW<Snctl1Spec> {
        NrwtenW::new(self, 13)
    }
    #[doc = "Bit 14 - Extended mode enable"]
    #[inline(always)]
    #[must_use]
    pub fn exmoden(&mut self) -> ExmodenW<Snctl1Spec> {
        ExmodenW::new(self, 14)
    }
    #[doc = "Bit 15 - Asynchronous wait"]
    #[inline(always)]
    #[must_use]
    pub fn asyncwait(&mut self) -> AsyncwaitW<Snctl1Spec> {
        AsyncwaitW::new(self, 15)
    }
    #[doc = "Bits 16:18 - CRAM page size"]
    #[inline(always)]
    #[must_use]
    pub fn cps(&mut self) -> CpsW<Snctl1Spec> {
        CpsW::new(self, 16)
    }
    #[doc = "Bit 19 - Synchronous write"]
    #[inline(always)]
    #[must_use]
    pub fn syncwr(&mut self) -> SyncwrW<Snctl1Spec> {
        SyncwrW::new(self, 19)
    }
}
#[doc = "SRAM/NOR flash control register 1\n\nYou can [`read`](crate::generic::Reg::read) this register and get [`snctl1::R`](R).  You can [`reset`](crate::generic::Reg::reset), [`write`](crate::generic::Reg::write), [`write_with_zero`](crate::generic::Reg::write_with_zero) this register using [`snctl1::W`](W). You can also [`modify`](crate::generic::Reg::modify) this register. See [API](https://docs.rs/svd2rust/#read--modify--write-api)."]
pub struct Snctl1Spec;
impl crate::RegisterSpec for Snctl1Spec {
    type Ux = u32;
}
#[doc = "`read()` method returns [`snctl1::R`](R) reader structure"]
impl crate::Readable for Snctl1Spec {}
#[doc = "`write(|w| ..)` method takes [`snctl1::W`](W) writer structure"]
impl crate::Writable for Snctl1Spec {
    type Safety = crate::Unsafe;
    const ZERO_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
    const ONE_TO_MODIFY_FIELDS_BITMAP: u32 = 0;
}
#[doc = "`reset()` method sets SNCTL1 to value 0x30d2"]
impl crate::Resettable for Snctl1Spec {
    const RESET_VALUE: u32 = 0x30d2;
}
